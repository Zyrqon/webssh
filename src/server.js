const express = require('express');
const { Client } = require('ssh2');
const WebSocket = require('ws');
const fs = require('fs');
const path = require('path');
const { v4: uuidv4, validate: uuidValidate } = require('uuid');
const crypto = require('crypto');
const QRCode = require('qrcode');
const rateLimit = require('express-rate-limit');
const helmet = require('helmet');
const cookieParser = require('cookie-parser');
const csrf = require('csurf');
const session = require('express-session');
const ipaddr = require('ipaddr.js');
const validator = require('validator');
const xss = require('xss');
const { authenticator } = require('otplib');
const LRU = require('lru-cache');
const winston = require('winston');

const MIN_PASSWORD_LENGTH = 12;
const MAX_REQUEST_SIZE = '100kb';

const apiLimiter = rateLimit({
  windowMs: 15 * 60 * 1000,
  max: 100,
  message: { error: 'Слишком много запросов. Попробуйте позже.' },
  standardHeaders: true,
  legacyHeaders: false
});

const loginLimiter = rateLimit({
   windowMs: 15 * 60 * 1000,
   max: 10,
   message: { error: 'Слишком много попыток входа. Попробуйте позже.' },
   standardHeaders: true,
   legacyHeaders: false
});

// ✓ MEDIUM #12: Add rate limiting for 2FA setup to prevent brute force
const setup2faLimiter = rateLimit({
   windowMs: 15 * 60 * 1000,
   max: 10,
   message: { error: 'Слишком много попыток настройки 2FA. Попробуйте позже.' },
   standardHeaders: true,
   legacyHeaders: false
});

// ✓ LOW #20: Add rate limiter for profile updates
const profileUpdateLimiter = rateLimit({
   windowMs: 15 * 60 * 1000,
   max: 10,  // Max 10 profile updates per 15 minutes
   message: { error: 'Слишком много обновлений профиля. Попробуйте позже.' },
   standardHeaders: true,
   legacyHeaders: false
});

const loginAttempts = new Map();

function getLoginAttempts(userId) {
  return loginAttempts.get(userId) || { count: 0, lockedUntil: 0 };
}

function incrementLoginAttempts(userId) {
  const attempts = getLoginAttempts(userId);
  attempts.count++;
  if (attempts.count >= 5) {
    attempts.lockedUntil = Date.now() + 15 * 60 * 1000;
  }
  loginAttempts.set(userId, attempts);
}

function clearLoginAttempts(userId) {
  loginAttempts.delete(userId);
}

function parseCookies(cookieHeader) {
  const result = {};
  if (!cookieHeader) return result;
  const parts = cookieHeader.split(';');
  for (const part of parts) {
    const idx = part.indexOf('=');
    if (idx === -1) continue;
    const key = part.slice(0, idx).trim();
    const value = part.slice(idx + 1).trim();
    if (!key) continue;
    result[key] = decodeURIComponent(value);
  }
  return result;
}

function setCookie(res, name, value, opts = {}) {
  const parts = [];
  parts.push(`${name}=${encodeURIComponent(value)}`);
  parts.push(`Path=${opts.path || '/'}`);
  if (opts.httpOnly) parts.push('HttpOnly');
  if (opts.secure) parts.push('Secure');
   parts.push(`SameSite=${opts.sameSite || 'Strict'}`);
  if (typeof opts.maxAgeSeconds === 'number') parts.push(`Max-Age=${Math.floor(opts.maxAgeSeconds)}`);
  if (opts.expires) parts.push(`Expires=${opts.expires.toUTCString()}`);

  const existing = res.getHeader('Set-Cookie');
  const next = Array.isArray(existing) ? existing.concat(parts.join('; ')) : (existing ? [existing, parts.join('; ')] : parts.join('; '));
  res.setHeader('Set-Cookie', next);
}

function clearCookie(res, name) {
   setCookie(res, name, '', { path: '/', httpOnly: true, sameSite: 'Strict', expires: new Date(0) });
}

function randomToken(bytes = 32) {
  return crypto.randomBytes(bytes).toString('base64url');
}

function hashPasswordScrypt(password) {
  const salt = crypto.randomBytes(16);
  const hash = crypto.scryptSync(password, salt, 64);
  return `scrypt$${salt.toString('base64')}$${hash.toString('base64')}`;
}

function verifyPassword(user, password) {
  if (user.passwordHash && typeof user.passwordHash === 'string') {
    const parts = user.passwordHash.split('$');
    if (parts.length === 3 && parts[0] === 'scrypt') {
      const salt = Buffer.from(parts[1], 'base64');
      const expected = Buffer.from(parts[2], 'base64');
      const actual = crypto.scryptSync(password, salt, expected.length);
      return crypto.timingSafeEqual(expected, actual);
    }
  }

  if (user.password && typeof user.password === 'string') {
    const legacy = crypto.createHash('sha256').update(password).digest('hex');
    // ✓ Использовать timing-safe сравнение для legacy паролей
    try {
      return crypto.timingSafeEqual(
        Buffer.from(legacy, 'hex'),
        Buffer.from(user.password, 'hex')
      );
    } catch (e) {
      // Если формат некорректен, вернуть false
      return false;
    }
  }

  return false;
}

function generateTOTPSecret() {
  return authenticator.generateSecret({
    name: 'WebSSH',
    issuer: 'WebSSH'
  });
}

function generateTOTPUri(secret, account) {
  return authenticator.keyuri(account, 'WebSSH', secret);
}

function verifyTOTP(secret, token, userId) {
   try {
     const isValid = authenticator.verify({
       secret: secret,
       encoding: 'base32',
       token: token,
       window: 1
     });
     
     if (!isValid) return false;
     
     // ✓ HIGH #10: Check for TOTP code replay attack
     const codeKey = `${userId}:${token}`;
     if (usedTOTPCodes.has(codeKey)) {
       return false; // Code already used
     }
     
     // Mark code as used for 90 seconds (3 TOTP windows)
     usedTOTPCodes.set(codeKey, Date.now());
     setTimeout(() => usedTOTPCodes.delete(codeKey), 90 * 1000);
     
     return true;
   } catch (e) {
     return false;
   }
}

const app = express();
const PORT = Number.parseInt(process.env.PORT || '3000', 10);
const HOST = process.env.HOST || '127.0.0.1';
const USERS_FILE = path.join(__dirname, 'users.json');
const SESSIONS_FILE = path.join(__dirname, 'sessions.json');
const MASTER_KEY_FILE = path.join(__dirname, '.master_key');
const SESSION_COOKIE = 'webssh_session';
const SESSION_TTL_SECONDS = 60 * 60 * 4; // 4 часа
// ✓ MEDIUM #11: Add absolute session timeout
const SESSION_ABSOLUTE_TIMEOUT = 24 * 60 * 60 * 1000; // 24 hours max lifetime
const LOGS_DIR = process.env.LOGS_DIR || path.join(__dirname, '../logs');
const AUDIT_LOG_FILE = path.join(LOGS_DIR, 'audit.log');

const sessions = new LRU({
   max: 10000,
   ttl: SESSION_TTL_SECONDS * 1000,
   updateAgeOnGet: true
});

// ✓ MEDIUM #11: Track session creation time for absolute timeout
const sessionCreatedAt = new Map();

const loginChallenges = new LRU({
   max: 5000,
   ttl: 10 * 60 * 1000,
   updateAgeOnGet: true
});

// ✓ HIGH #10: TOTP replay protection - track used codes per user
const usedTOTPCodes = new Map();

const wsConnections = new LRU({
   max: 20000,
   ttl: 60 * 60 * 1000,
   updateAgeOnGet: true
});

// Rate limiting для WebSocket сообщений
const wsMessageLimiters = new Map();

const LOGIN_CHALLENGES_FILE = path.join(__dirname, 'login_challenges.json');

function sanitizeInput(str, maxLength = 255) {
  if (typeof str !== 'string') return '';
  // Санитизировать от XSS
  return xss(str.trim().slice(0, maxLength), {
    whiteList: {},
    stripIgnoredTag: true,
    stripLeakedHtml: true
  });
}

// Валидация UUID
function isValidUserId(userId) {
  return uuidValidate(userId);
}

// Валидация SSH порта
function isValidPort(port) {
  const portNum = parseInt(port, 10);
  return Number.isInteger(portNum) && portNum >= 1 && portNum <= 65535;
}

// ✓ MEDIUM #16: Enhanced username validation
const RESERVED_USERNAMES = [
   'admin', 'root', 'system', 'test', 'administrator',
   'moderator', 'support', 'api', 'dev', 'developer',
   'localhost', 'webssh', 'guest', 'user', 'username',
   'null', 'undefined', 'anonymous', 'public', 'private'
];

function isValidUsername(username) {
   if (!username || typeof username !== 'string') return false;
   if (username.length < 3 || username.length > 32) return false;
   if (!/^[a-zA-Z0-9_-]+$/.test(username)) return false;
   
   // Check for reserved usernames (case-insensitive)
   if (RESERVED_USERNAMES.includes(username.toLowerCase())) {
     return false;
   }
   
   // Check for Unicode confusables (normalization)
   const normalized = username.normalize('NFKC');
   if (normalized !== username) {
     return false;  // Contains confusable Unicode characters
   }
   
   return true;
}

// ✓ HIGH #8: Validate SSH private key format
function validatePrivateKey(privateKey) {
   if (!privateKey || typeof privateKey !== 'string') return false;
   
   // Check for valid key format markers
   if (!privateKey.includes('BEGIN') || !privateKey.includes('END')) {
     return false;
   }
   
   // Reject encrypted/passphrase-protected keys
   if (privateKey.includes('ENCRYPTED') || privateKey.includes('ENCRYPTED RSA') || privateKey.includes('pass')) {
     return false;
   }
   
   // Check for known key types
   const validTypes = [
     'BEGIN RSA PRIVATE KEY',
     'BEGIN DSA PRIVATE KEY',
     'BEGIN EC PRIVATE KEY',
     'BEGIN OPENSSH PRIVATE KEY',
     'BEGIN PRIVATE KEY'
   ];
   
   return validTypes.some(type => privateKey.includes(type));
}

// Белый список разрешённых SSH хостов
const ALLOWED_SSH_HOSTS = process.env.ALLOWED_SSH_HOSTS 
  ? process.env.ALLOWED_SSH_HOSTS.split(',').map(h => h.trim())
  : [];

// Проверка разрешённого хоста
function isAllowedSshHost(host) {
  if (!host || typeof host !== 'string') return false;
  
  // Если нет белого списка - разрешить все публичные адреса (кроме локальных)
  try {
    const addr = ipaddr.process(host);
    
    // Запретить private IP адреса (локальные)
    if (addr.range() === 'private' || addr.range() === 'loopback' || addr.range() === 'unspecified') {
      return false;
    }
    
    // Если есть белый список - проверить в нём
    if (ALLOWED_SSH_HOSTS.length > 0) {
      return ALLOWED_SSH_HOSTS.includes(host.toLowerCase());
    }
    
    return true;
  } catch (e) {
    // Если это не IP - проверить как доменное имя в белом списке
    if (ALLOWED_SSH_HOSTS.length === 0) {
      return true; // Если нет черного списка - разрешить
    }
    return ALLOWED_SSH_HOSTS.includes(host.toLowerCase());
  }
}

// Инициализация директории логов
if (!fs.existsSync(LOGS_DIR)) {
  fs.mkdirSync(LOGS_DIR, { mode: 0o700, recursive: true });
}

// Установить правильные разрешения
try {
  fs.chmodSync(LOGS_DIR, 0o700);
} catch (err) {
  console.error('Failed to set log directory permissions:', err);
}

function auditLog(action, userId, details = {}) {
  const entry = {
    timestamp: new Date().toISOString(),
    action,
    userId,
    ...details
  };
  try {
    // Не логировать чувствительные данные
    const safeEntry = { ...entry };
    if (safeEntry.password) safeEntry.password = '[REDACTED]';
    if (safeEntry.privateKey) safeEntry.privateKey = '[REDACTED]';
    if (safeEntry.passphrase) safeEntry.passphrase = '[REDACTED]';
    if (safeEntry.token) safeEntry.token = '[REDACTED]';
    
    fs.appendFileSync(AUDIT_LOG_FILE, JSON.stringify(safeEntry) + '\n', { mode: 0o600 });
  } catch (_) {}
}

function getMasterKey() {
   let secret = process.env.WEBSSH_SECRET;
   if (!secret) {
     if (fs.existsSync(MASTER_KEY_FILE)) {
       secret = fs.readFileSync(MASTER_KEY_FILE, 'utf8').trim();
     } else {
       secret = randomToken(48);
       try {
         // ✓ CRITICAL #5: Use 'wx' flag for atomic exclusive write
         // 'wx' = write + exclusive (fail if file exists)
         const fd = fs.openSync(MASTER_KEY_FILE, 'wx', 0o600);
         try {
           fs.writeSync(fd, secret + '\n');
         } finally {
           fs.closeSync(fd);
         }
       } catch (err) {
         // ✓ If file already exists (race condition), read it
         if (err.code === 'EEXIST' && fs.existsSync(MASTER_KEY_FILE)) {
           secret = fs.readFileSync(MASTER_KEY_FILE, 'utf8').trim();
         } else {
           throw err;
         }
       }
     }
   }
   return crypto.createHash('sha256').update(secret, 'utf8').digest();
}

const MASTER_KEY = getMasterKey();

function encryptSecret(plainText) {
  if (plainText == null) return null;
  const text = String(plainText);
  const iv = crypto.randomBytes(12);
  const cipher = crypto.createCipheriv('aes-256-gcm', MASTER_KEY, iv);
  const enc = Buffer.concat([cipher.update(text, 'utf8'), cipher.final()]);
  const tag = cipher.getAuthTag();
  return `enc$${iv.toString('base64')}$${tag.toString('base64')}$${enc.toString('base64')}`;
}

function decryptSecret(payload) {
   if (!payload) return null;
   if (typeof payload !== 'string') return null;
   // ✓ HIGH #9: Validate input size to prevent DoS via large payloads
   if (payload.length > 100000) return null; // Max 100KB encrypted data
   if (!payload.startsWith('enc$')) return payload; // legacy/plain
   const parts = payload.split('$');
   if (parts.length !== 4) return null;
   try {
     const iv = Buffer.from(parts[1], 'base64');
     const tag = Buffer.from(parts[2], 'base64');
     const data = Buffer.from(parts[3], 'base64');
     // Validate buffer sizes
     if (iv.length !== 12 || tag.length !== 16) return null;
     const decipher = crypto.createDecipheriv('aes-256-gcm', MASTER_KEY, iv);
     decipher.setAuthTag(tag);
     const plain = Buffer.concat([decipher.update(data), decipher.final()]);
     return plain.toString('utf8');
   } catch (e) {
     // Catch decryption errors and return null instead of throwing
     return null;
   }
}

function loadSessionsFromDisk() {
  if (!fs.existsSync(SESSIONS_FILE)) return;
  try {
    const raw = JSON.parse(fs.readFileSync(SESSIONS_FILE, 'utf8'));
    if (!Array.isArray(raw)) return;
    for (const s of raw) {
      if (!s || typeof s !== 'object') continue;
      if (!s.id || !s.userId || typeof s.expiresAtMs !== 'number') continue;
      sessions.set(s.id, { userId: s.userId, expiresAtMs: s.expiresAtMs });
    }
  } catch (_) {}
}

function saveSessionsToDisk() {
  try {
    const data = [];
    for (const [id, s] of sessions) data.push({ id, userId: s.userId, expiresAtMs: s.expiresAtMs });
    try {
      fs.writeFileSync(SESSIONS_FILE, JSON.stringify(data, null, 2), { mode: 0o600 });
    } catch (_) {
      fs.writeFileSync(SESSIONS_FILE, JSON.stringify(data, null, 2));
    }
  } catch (_) {}
}

loadSessionsFromDisk();

function loadLoginChallengesFromDisk() {
  if (!fs.existsSync(LOGIN_CHALLENGES_FILE)) return;
  try {
    const raw = JSON.parse(fs.readFileSync(LOGIN_CHALLENGES_FILE, 'utf8'));
    if (!Array.isArray(raw)) return;
    for (const c of raw) {
      if (!c || typeof c !== 'object') continue;
      if (!c.id || !c.userId || typeof c.expiresAtMs !== 'number') continue;
      loginChallenges.set(c.id, { userId: c.userId, expiresAtMs: c.expiresAtMs });
    }
  } catch (_) {}
}

function saveLoginChallengesToDisk() {
  try {
    const data = [];
    for (const [id, c] of loginChallenges) data.push({ id, userId: c.userId, expiresAtMs: c.expiresAtMs });
    fs.writeFileSync(LOGIN_CHALLENGES_FILE, JSON.stringify(data, null, 2));
  } catch (_) {}
}

loadLoginChallengesFromDisk();

function cleanupMaps() {
  const now = Date.now();
  let sessionsChanged = false;
  for (const [k, v] of sessions) {
    if (!v || v.expiresAtMs <= now) {
      sessions.delete(k);
      sessionsChanged = true;
    }
  }
  let challengesChanged = false;
  for (const [k, v] of loginChallenges) {
    if (!v || v.expiresAtMs <= now) {
      loginChallenges.delete(k);
      challengesChanged = true;
    }
  }
  if (sessionsChanged) saveSessionsToDisk();
  if (challengesChanged) saveLoginChallengesToDisk();
}

setInterval(cleanupMaps, 60_000).unref?.();

// Middleware для HTTPS redirect
app.use((req, res, next) => {
  // Проверить X-Forwarded-Proto (для proxy/load balancer)
  const proto = req.get('x-forwarded-proto') || req.protocol;
  if (proto !== 'https' && process.env.NODE_ENV === 'production') {
    // ✓ Валидировать Host header перед использованием
    const hostHeader = req.get('host');
    if (!hostHeader || hostHeader.includes('/')) {
      return res.status(400).send('Invalid Host header');
    }
    
    // ✓ Опционально: проверить whitelist хостов
    const allowedHosts = (process.env.ALLOWED_HOSTS || '')
      .split(',')
      .map(h => h.trim())
      .filter(Boolean);
    
    if (allowedHosts.length > 0) {
      const hostname = hostHeader.split(':')[0];
      if (!allowedHosts.includes(hostname)) {
        return res.status(400).send('Invalid Host');
      }
    }
    
    return res.redirect(301, `https://${hostHeader}${req.url}`);
  }
  next();
});

// HSTS заголовок
app.use((req, res, next) => {
  res.setHeader('Strict-Transport-Security', 'max-age=31536000; includeSubDomains; preload');
  next();
});

app.use(helmet({
   contentSecurityPolicy: {
     directives: {
       defaultSrc: ["'self'"],
       // ✓ MEDIUM #15: Allow CDN resources with SRI integrity checks
       scriptSrc: ["'self'", 'https://cdn.jsdelivr.net'],
       styleSrc: ["'self'", 'https://cdn.jsdelivr.net'],
       imgSrc: ["'self'", 'data:'],
       connectSrc: ["'self'"],
       upgradeInsecureRequests: []
     }
   },
   crossOriginEmbedderPolicy: false,
   hsts: {
     maxAge: 31536000,
     includeSubDomains: true,
     preload: true
   }
}));

app.use(cookieParser());
app.use(express.json({ limit: MAX_REQUEST_SIZE }));

// CSRF защита
app.use(csrf({ cookie: true }));

// CSRF токен для GET запросов
app.get('/api/csrf-token', (req, res) => {
  res.json({ csrfToken: req.csrfToken() });
});

app.use(express.static(path.join(__dirname, '..', 'public')));

function loadUsers() {
  if (!fs.existsSync(USERS_FILE)) {
    const defaultUsers = [{
      id: uuidv4(),
      username: 'admin',
      passwordHash: hashPasswordScrypt('admin'),
      totpSecret: null,
      created: new Date().toISOString()
    }];
    fs.writeFileSync(USERS_FILE, JSON.stringify(defaultUsers, null, 2));
    return defaultUsers;
  }
  return JSON.parse(fs.readFileSync(USERS_FILE, 'utf8'));
}

function saveUsers(users) {
  fs.writeFileSync(USERS_FILE, JSON.stringify(users, null, 2));
}

function loadConnections(userId) {
  // Валидация userId - защита от Path Traversal
  if (!isValidUserId(userId)) {
    throw new Error('Invalid userId format');
  }
  
  const file = path.join(__dirname, `connections_${userId}.json`);
  if (!fs.existsSync(file)) return [];
  let connections = JSON.parse(fs.readFileSync(file, 'utf8'));
  if (!Array.isArray(connections)) connections = [];

  // Migration:
  // - legacy plaintext `password` / `privateKey` -> encrypted fields
  // - keep compatibility with already-encrypted fields
  let changed = false;
  const migrated = connections.map((c) => {
    if (!c || typeof c !== 'object') return c;
    const next = { ...c };
    if (typeof next.password === 'string' && !next.passwordEnc) {
      next.passwordEnc = encryptSecret(next.password);
      delete next.password;
      changed = true;
    }
    if (typeof next.privateKey === 'string' && !next.privateKeyEnc) {
      next.privateKeyEnc = encryptSecret(next.privateKey);
      delete next.privateKey;
      changed = true;
    }
    return next;
  });
  if (changed) {
    try {
      fs.writeFileSync(file, JSON.stringify(migrated, null, 2));
    } catch (_) {}
  }
  return migrated;
}

function saveConnections(userId, connections) {
  // Валидация userId
  if (!isValidUserId(userId)) {
    throw new Error('Invalid userId format');
  }
  
  const file = path.join(__dirname, `connections_${userId}.json`);
  fs.writeFileSync(file, JSON.stringify(connections, null, 2));
}

function getSessionUserId(req) {
   const cookies = parseCookies(req.headers.cookie);
   const sessionId = cookies[SESSION_COOKIE];
   if (!sessionId) return null;
   
   // ✓ MEDIUM #11: Check absolute session timeout
   const createdAt = sessionCreatedAt.get(sessionId);
   if (createdAt && Date.now() - createdAt > SESSION_ABSOLUTE_TIMEOUT) {
     sessions.delete(sessionId);
     sessionCreatedAt.delete(sessionId);
     return null;
   }
   
   const session = sessions.get(sessionId);
   if (!session) return null;
   if (session.expiresAtMs <= Date.now()) {
     sessions.delete(sessionId);
     sessionCreatedAt.delete(sessionId);
     return null;
   }
   return session.userId;
}

function requireAuth(req, res, next) {
  const userId = getSessionUserId(req);
  if (!userId) return res.status(401).json({ error: 'Требуется авторизация' });
  req.userId = userId;
  next();
}

function createSession(res, userId, req) {
   const cookies = parseCookies(req?.headers?.cookie);
   const oldSessionId = cookies[SESSION_COOKIE];
   if (oldSessionId) {
     sessions.delete(oldSessionId);
     sessionCreatedAt.delete(oldSessionId);
   }
   
   const sessionId = randomToken(32);
   sessions.set(sessionId, { userId, expiresAtMs: Date.now() + SESSION_TTL_SECONDS * 1000 });
   // ✓ MEDIUM #11: Track session creation time for absolute timeout
   sessionCreatedAt.set(sessionId, Date.now());
   saveSessionsToDisk();
   const secure = req?.socket?.encrypted === true || process.env.WEBSSH_COOKIE_SECURE === '1';
    // ✓ MEDIUM #13: Use SameSite=Strict to prevent CSRF
    setCookie(res, SESSION_COOKIE, sessionId, {
      path: '/',
      httpOnly: true,
      secure,
      sameSite: 'Strict',
      maxAgeSeconds: SESSION_TTL_SECONDS
    });
}

const PUBLIC_DIR = path.join(__dirname, '..', 'public');

app.get('/', (req, res) => res.sendFile(path.join(PUBLIC_DIR, 'index.html')));
app.get('/login', (req, res) => res.sendFile(path.join(PUBLIC_DIR, 'login.html')));
app.get('/connect', (req, res) => res.sendFile(path.join(PUBLIC_DIR, 'client.html')));

// Backward compatible URLs
app.get('/login.html', (req, res) => res.redirect(302, '/login'));
app.get('/client.html', (req, res) => res.redirect(302, '/connect'));

app.post('/api/register', (req, res) => {
  const { username, password } = req.body;
  
  // Валидация входных данных
  if (!username || !password) {
    return res.status(400).json({ error: 'Fill all fields' });
  }
  
  // Валидация username
  if (!isValidUsername(username)) {
    return res.status(400).json({ error: 'Username must be 3-32 characters, alphanumeric with - and _' });
  }
  
  // Валидация пароля
  if (typeof password !== 'string' || password.length < MIN_PASSWORD_LENGTH) {
    return res.status(400).json({ error: `Password must be at least ${MIN_PASSWORD_LENGTH} characters` });
  }
  
  // Проверить сложность пароля (минимум 3 из 4: заглавные, строчные, цифры, спецсимволы)
  const hasUppercase = /[A-Z]/.test(password);
  const hasLowercase = /[a-z]/.test(password);
  const hasDigits = /\d/.test(password);
  const hasSpecial = /[!@#$%^&*()_+\-=\[\]{};':"\\|,.<>\/?]/.test(password);
  const complexityScore = [hasUppercase, hasLowercase, hasDigits, hasSpecial].filter(Boolean).length;
  
  if (complexityScore < 3) {
    return res.status(400).json({ error: 'Password must contain at least 3 of: uppercase, lowercase, numbers, special characters' });
  }
  
  const users = loadUsers();
  if (users.find(u => u.username.toLowerCase() === username.toLowerCase())) {
    return res.status(400).json({ error: 'Username already taken' });
  }
  
  const newUser = {
    id: uuidv4(),
    username: sanitizeInput(username),
    passwordHash: hashPasswordScrypt(password),
    totpSecret: null,
    created: new Date().toISOString()
  };
  users.push(newUser);
  saveUsers(users);
  
  saveConnections(newUser.id, []);
  
  // Очистить старые сессии перед созданием новой (защита от session fixation)
  req.session = {};
  
  createSession(res, newUser.id, req);
  
  auditLog('user_registered', newUser.id, { username: newUser.username });
  
  res.json({ username: newUser.username });
});

app.use('/api/', apiLimiter);

app.post('/api/check-username', (req, res) => {
  const { username } = req.body;
  if (!username) return res.json({ available: false });
  const users = loadUsers();
  const available = !users.find(u => u.username.toLowerCase() === username.toLowerCase());
  res.json({ available });
});

app.post('/api/register-with-2fa', (req, res) => {
  const { username, password, code, secret } = req.body;
  if (!username || !password || !code || !secret) {
    return res.status(400).json({ error: 'Не все поля заполнены' });
  }
  if (typeof password !== 'string' || password.length < MIN_PASSWORD_LENGTH) {
    return res.status(400).json({ error: `Минимальная длина пароля — ${MIN_PASSWORD_LENGTH} символов` });
  }
  
  const users = loadUsers();
  if (users.find(u => u.username.toLowerCase() === username.toLowerCase())) {
    return res.status(400).json({ error: 'Такое имя пользователя уже занято' });
   }
   
   // ✓ HIGH #10: Use username as temp ID for TOTP replay protection during registration
   const isValid = verifyTOTP(secret, code, `temp:${username}`);
   
   if (!isValid) {
     return res.status(401).json({ error: 'Неверный код' });
   }
  
  const newUser = {
    id: uuidv4(),
    username,
    passwordHash: hashPasswordScrypt(password),
    totpSecret: secret,
    created: new Date().toISOString()
  };
  users.push(newUser);
  saveUsers(users);
  
  saveConnections(newUser.id, []);
  
  createSession(res, newUser.id, req);
  res.json({ username: newUser.username });
});

app.post('/api/login', loginLimiter, (req, res) => {
  const { username, password } = req.body;
  const users = loadUsers();
  const user = users.find(u => u.username.toLowerCase() === username.toLowerCase());
  
  // Использовать одинаковое сообщение об ошибке для всех ошибок входа
  const loginFailed = () => {
    // Задержка для замедления brute force
    setTimeout(() => {
      res.status(401).json({ error: 'Invalid username or password' });
    }, Math.random() * 300 + 200);
  };
  
  if (!user || !verifyPassword(user, password)) {
    if (user) {
      incrementLoginAttempts(user.id);
      auditLog('login_failed', user.id, { username, reason: 'invalid_password' });
    } else {
      auditLog('login_failed_unknown_user', null, { username });
    }
    return loginFailed();
  }

  const attempts = getLoginAttempts(user.id);
  if (attempts.lockedUntil > Date.now()) {
    return res.status(429).json({ error: 'Account locked. Try again later.' });
  }
  
  // Миграция старых SHA256 паролей на scrypt
  if (user.password && !user.passwordHash) {
    user.passwordHash = hashPasswordScrypt(password);
    delete user.password;
    saveUsers(users);
    auditLog('password_migrated', user.id, { method: 'sha256_to_scrypt' });
  }
  
  if (user.totpSecret) {
    const challenge = randomToken(24);
    loginChallenges.set(challenge, { userId: user.id, expiresAtMs: Date.now() + 5 * 60 * 1000 });
    saveLoginChallengesToDisk();
    return res.json({ requires2fa: true, challenge });
  }
  
  clearLoginAttempts(user.id);
  createSession(res, user.id, req);
  auditLog('login_success', user.id, { username: user.username });
  res.json({ username: user.username });
});

app.post('/api/login-2fa', loginLimiter, (req, res) => {
  const { challenge, code } = req.body;
  if (!challenge || !code) return res.status(400).json({ error: 'Не все поля заполнены' });
  
  const users = loadUsers();
  const ch = loginChallenges.get(challenge);
  if (!ch || ch.expiresAtMs <= Date.now()) return res.status(401).json({ error: 'Сессия входа истекла. Войдите заново.' });
  const user = users.find(u => u.id === ch.userId);
  if (!user) return res.status(404).json({ error: 'Пользователь не найден' });
  
  if (!user.totpSecret) return res.status(400).json({ error: 'Двухфакторная аутентификация не настроена' });
  
   const isValid = verifyTOTP(user.totpSecret, code, user.id);
   if (!isValid) {
     incrementLoginAttempts(user.id);
     auditLog('login_2fa_failed', user.id, { challenge });
     return res.status(401).json({ error: 'Неверный код' });
   }
  
  clearLoginAttempts(user.id);
  loginChallenges.delete(challenge);
  saveLoginChallengesToDisk();
  createSession(res, user.id, req);
  auditLog('login_2fa_success', user.id, {});
  res.json({ username: user.username });
});

app.post('/api/logout', (req, res) => {
  const userId = getSessionUserId(req);
  const cookies = parseCookies(req.headers.cookie);
  const sessionId = cookies[SESSION_COOKIE];
  if (sessionId) {
    sessions.delete(sessionId);
    saveSessionsToDisk();
    auditLog('logout', userId, {});
  }
  clearCookie(res, SESSION_COOKIE);
  res.json({ success: true });
});

app.post('/api/setup-2fa', setup2faLimiter, async (req, res) => {
  const userId = getSessionUserId(req);
  if (!userId) {
    const username = req.body.username;
    if (!username) return res.status(400).json({ error: 'Укажите имя пользователя' });
    
    const secret = generateTOTPSecret();
    const otpauth = generateTOTPUri(secret, username);
    const qrCodeDataUrl = await QRCode.toDataURL(otpauth);
    
    return res.json({ secret, qrCode: qrCodeDataUrl });
  }
  
  const users = loadUsers();
  const idx = users.findIndex(u => u.id === userId);
  if (idx === -1) return res.status(404).json({ error: 'Пользователь не найден' });
  
  if (users[idx].totpSecret) {
    return res.status(400).json({ error: '2FA уже включена. Отключите её, чтобы настроить заново.' });
  }
  
  const secret = generateTOTPSecret();
  users[idx].totpPendingSecret = secret;
  saveUsers(users);
  
  const otpauth = generateTOTPUri(secret, users[idx].username);
  const qrCodeDataUrl = await QRCode.toDataURL(otpauth);
  
  res.json({ qrCode: qrCodeDataUrl });
});

app.post('/api/verify-2fa', (req, res) => {
  const userId = getSessionUserId(req);
  const { code } = req.body;
  if (!userId || !code) return res.status(400).json({ error: 'Не все поля заполнены' });
  
  const users = loadUsers();
  const idx = users.findIndex(u => u.id === userId);
  if (idx === -1) return res.status(404).json({ error: 'Пользователь не найден' });
  
  const user = users[idx];
  
   if (user.totpPendingSecret) {
     if (!verifyTOTP(user.totpPendingSecret, code, userId)) {
       return res.status(401).json({ error: 'Неверный код' });
     }
     user.totpSecret = user.totpPendingSecret;
     user.totpPendingSecret = null;
     saveUsers(users);
     return res.json({ success: true });
   }
   
   if (!user.totpSecret) {
     return res.status(400).json({ error: 'Сначала начните настройку 2FA в профиле' });
   }
   
   if (!verifyTOTP(user.totpSecret, code, userId)) return res.status(401).json({ error: 'Неверный код' });
  
  res.json({ success: true });
});

app.post('/api/verify-2fa-temp', (req, res) => {
   const { code, secret } = req.body;
   if (!code || !secret) return res.status(400).json({ error: 'Missing fields' });
   // ✓ HIGH #10: Use hash of secret as temp ID for TOTP replay protection
   const tempId = crypto.createHash('sha256').update(secret).digest('hex').substring(0, 16);
   if (!verifyTOTP(secret, code, tempId)) return res.status(401).json({ error: 'Invalid code' });
   res.json({ success: true });
});

app.post('/api/enable-2fa', requireAuth, (req, res) => {
   const { secret, code } = req.body;
   if (!secret || !code) return res.status(400).json({ error: 'Missing fields' });
   
   if (!verifyTOTP(secret, code, req.userId)) {
     return res.status(401).json({ error: 'Invalid code' });
   }
   
   const users = loadUsers();
   const idx = users.findIndex(u => u.id === req.userId);
   if (idx === -1) return res.status(404).json({ error: 'User not found' });
   
   users[idx].totpSecret = secret;
   saveUsers(users);
   res.json({ success: true });
});

app.post('/api/disable-2fa', (req, res) => {
  const userId = getSessionUserId(req);
  const { password } = req.body;
  if (!userId || !password) return res.status(400).json({ error: 'Не все поля заполнены' });
  
  const users = loadUsers();
  const idx = users.findIndex(u => u.id === userId);
  if (idx === -1) return res.status(404).json({ error: 'Пользователь не найден' });
  
  if (!verifyPassword(users[idx], password)) {
    return res.status(401).json({ error: 'Неверный пароль' });
  }

  if (users[idx].password && !users[idx].passwordHash) {
    users[idx].passwordHash = hashPasswordScrypt(password);
    delete users[idx].password;
  }
  
  users[idx].totpSecret = null;
  users[idx].totpPendingSecret = null;
  saveUsers(users);
  
  res.json({ success: true });
});

app.post('/api/delete-account', (req, res) => {
  const userId = getSessionUserId(req);
  const { password } = req.body;
  if (!userId || !password) return res.status(400).json({ error: 'Не все поля заполнены' });
  
  const users = loadUsers();
  const idx = users.findIndex(u => u.id === userId);
  if (idx === -1) return res.status(404).json({ error: 'Пользователь не найден' });
  
  if (!verifyPassword(users[idx], password)) {
    return res.status(401).json({ error: 'Неверный пароль' });
  }

  if (users[idx].password && !users[idx].passwordHash) {
    users[idx].passwordHash = hashPasswordScrypt(password);
    delete users[idx].password;
  }
  
  const userConnectionsFile = path.join(__dirname, `connections_${userId}.json`);
  if (fs.existsSync(userConnectionsFile)) {
    fs.unlinkSync(userConnectionsFile);
  }
  
  users.splice(idx, 1);
  saveUsers(users);
  
  res.json({ success: true });
});

app.get('/api/me', requireAuth, (req, res) => {
  const users = loadUsers();
  const user = users.find(u => u.id === req.userId);
  if (!user) return res.status(404).json({ error: 'Пользователь не найден' });
  res.json({ username: user.username });
});

app.get('/api/connections', requireAuth, (req, res) => {
  const userId = req.userId;
  
  const connections = loadConnections(userId);
  res.json(connections.map((c) => {
    if (!c || typeof c !== 'object') return c;
    const { passwordEnc, privateKeyEnc, password, privateKey, ...rest } = c;
    return rest;
  }));
});

app.get('/api/connections/:id', requireAuth, (req, res) => {
   const userId = req.userId;
   const connections = loadConnections(userId);
   const conn = connections.find(c => c && c.id === req.params.id);
   if (!conn) return res.status(404).json({ error: 'Не найдено' });
   
   const { passwordEnc, privateKeyEnc, ...rest } = conn;
   const result = { 
     ...rest,
     // ✓ Санитизировать текстовые поля перед отправкой клиенту
     name: sanitizeInput(rest.name),
     username: sanitizeInput(rest.username),
     host: sanitizeInput(rest.host)
   };
   
   // ✓ HIGH #11: Do NOT return decrypted passwords/keys to client
   // These secrets are only needed server-side for SSH connections
   // Client should not receive plaintext credentials
   if (conn.authType === 'password') {
     result.hasPassword = !!conn.passwordEnc;
   } else if (conn.authType === 'key') {
     result.hasPrivateKey = !!conn.privateKeyEnc;
   }
   
   res.json(result);
});

app.post('/api/connections', requireAuth, (req, res) => {
  const userId = req.userId;
  
  // Валидация входных данных
  const { name, host, port, username, authType, password, privateKey } = req.body;
  
  if (!name || !host || !username) {
    return res.status(400).json({ error: 'Missing required fields' });
  }
  
  // Валидация портуа (1-65535)
  const portNum = port || 22;
  if (!isValidPort(portNum)) {
    return res.status(400).json({ error: 'Port must be between 1 and 65535' });
  }
  
  // SSRF защита - проверить хост
  if (!isAllowedSshHost(host)) {
    auditLog('ssh_connection_blocked', userId, { host, reason: 'host_not_allowed' });
    return res.status(403).json({ error: 'Host not allowed' });
  }
  
  // Валидация authType
  if (authType && !['password', 'key'].includes(authType)) {
    return res.status(400).json({ error: 'Invalid authType' });
   }
   
   const finalAuthType = authType || 'password';
   
   // Валидация credentials
   if (finalAuthType === 'password' && !password) {
     return res.status(400).json({ error: 'Password required for password auth' });
   }
   
   if (finalAuthType === 'key' && !privateKey) {
     return res.status(400).json({ error: 'Private key required for key auth' });
   }
   
   // ✓ HIGH #8: Validate SSH key format
   if (finalAuthType === 'key' && privateKey) {
     if (!validatePrivateKey(privateKey)) {
       return res.status(400).json({ 
         error: 'Invalid or encrypted SSH key. Please provide an unencrypted private key in PEM format (RSA, DSA, EC, or OpenSSH format).' 
       });
     }
   }
  
  const connections = loadConnections(userId);
  const newConnection = {
    id: uuidv4(),
    name: sanitizeInput(name),
    host: host,
    port: portNum,
    username: username,
    authType: finalAuthType,
    passwordEnc: finalAuthType === 'password' && password ? encryptSecret(password) : null,
    privateKeyEnc: finalAuthType === 'key' && privateKey ? encryptSecret(privateKey) : null,
    created: new Date().toISOString()
  };
  
  connections.push(newConnection);
  saveConnections(userId, connections);
  
  auditLog('connection_created', userId, { 
    connectionId: newConnection.id, 
    host: host,
    authType: finalAuthType
  });
  
  const { passwordEnc, privateKeyEnc, ...publicConn } = newConnection;
  res.json(publicConn);
});

app.put('/api/connections/:id', requireAuth, (req, res) => {
   const userId = req.userId;
  
  const { host, port } = req.body;
  
  // Валидация портов
  if (port && !isValidPort(port)) {
    return res.status(400).json({ error: 'Port must be between 1 and 65535' });
  }
  
  // SSRF защита
  if (host && !isAllowedSshHost(host)) {
    return res.status(403).json({ error: 'Host not allowed' });
  }
  
  let connections = loadConnections(userId);
  const idx = connections.findIndex(c => c.id === req.params.id);
  if (idx === -1) return res.status(404).json({ error: 'Not found' });
  
  const prev = connections[idx];
  const nextAuthType = req.body.authType || prev.authType || 'password';

  connections[idx] = {
    ...prev,
    // ✓ Санитизировать текстовые поля перед сохранением
    name: sanitizeInput(req.body.name || prev.name),
    host: sanitizeInput(req.body.host || prev.host),
    username: sanitizeInput(req.body.username || prev.username),
    port: port || prev.port,
    authType: nextAuthType,
    updated: new Date().toISOString()
  };
   
   if (nextAuthType === 'key') {
     if (req.body.privateKey) {
       // ✓ HIGH #8: Validate SSH key format on update too
       if (!validatePrivateKey(req.body.privateKey)) {
         return res.status(400).json({ 
           error: 'Invalid or encrypted SSH key. Please provide an unencrypted private key in PEM format.' 
         });
       }
       connections[idx].privateKeyEnc = encryptSecret(req.body.privateKey);
     }
     connections[idx].passwordEnc = null;
   } else {
     if (req.body.password) connections[idx].passwordEnc = encryptSecret(req.body.password);
     connections[idx].privateKeyEnc = null;
   }
  
  saveConnections(userId, connections);
  
  auditLog('connection_updated', userId, { 
    connectionId: req.params.id,
    host: host || prev.host
  });
  
  const { passwordEnc, privateKeyEnc, ...publicConn } = connections[idx];
  res.json(publicConn);
});

app.delete('/api/connections/:id', requireAuth, (req, res) => {
  const userId = req.userId;
  
  let connections = loadConnections(userId);
  // ✓ Проверка принадлежности соединения пользователю
  const idx = connections.findIndex(c => c && c.id === req.params.id);
  if (idx === -1) return res.status(404).json({ error: 'Соединение не найдено' });
  
  // ✓ Убедиться что соединение существует перед удалением
  const conn = connections[idx];
  if (!conn) return res.status(404).json({ error: 'Соединение не найдено' });
  
  connections.splice(idx, 1);
  saveConnections(userId, connections);
  
  auditLog('connection_deleted', userId, { connectionId: req.params.id });
  res.json({ success: true });
});

app.post('/api/update-profile', profileUpdateLimiter, (req, res) => {
   const userId = getSessionUserId(req);
   if (!userId) return res.status(401).json({ error: 'Требуется авторизация' });
   
   const { username, currentPassword, newPassword } = req.body;
   if (!currentPassword) return res.status(400).json({ error: 'Введите текущий пароль' });
   
   const users = loadUsers();
   const idx = users.findIndex(u => u.id === userId);
   if (idx === -1) return res.status(404).json({ error: 'Пользователь не найден' });
   
   const user = users[idx];
   if (!verifyPassword(user, currentPassword)) {
     return res.status(401).json({ error: 'Неверный пароль' });
   }

   if (user.password && !user.passwordHash) {
     user.passwordHash = hashPasswordScrypt(currentPassword);
     delete user.password;
   }
   
   // ✓ CRITICAL #1: Sanitize username to prevent XSS
   if (username && username.toLowerCase() !== user.username.toLowerCase()) {
     const sanitizedUsername = sanitizeInput(username);
     if (!sanitizedUsername) {
       return res.status(400).json({ error: 'Invalid username format' });
     }
     
     if (users.find(u => u.username.toLowerCase() === sanitizedUsername.toLowerCase() && u.id !== userId)) {
       return res.status(400).json({ error: 'Такое имя пользователя уже занято' });
     }
     user.username = sanitizedUsername;
     
     // Log username change for audit trail
     auditLog('profile_username_changed', userId, { 
       oldUsername: users[idx].username,
       newUsername: sanitizedUsername
     });
   }
   
   // ✓ CRITICAL #2: Enforce password complexity on profile updates
   if (newPassword) {
     if (newPassword.length < MIN_PASSWORD_LENGTH) {
       return res.status(400).json({ error: `Минимальная длина пароля — ${MIN_PASSWORD_LENGTH} символов` });
     }
     
     const hasUppercase = /[A-Z]/.test(newPassword);
     const hasLowercase = /[a-z]/.test(newPassword);
     const hasDigits = /\d/.test(newPassword);
     const hasSpecial = /[!@#$%^&*()_+\-=\[\]{};':"\\|,.<>\/?]/.test(newPassword);
     const complexityScore = [hasUppercase, hasLowercase, hasDigits, hasSpecial].filter(Boolean).length;
     
     if (complexityScore < 3) {
       return res.status(400).json({ 
         error: 'Пароль должен содержать минимум 3 из: прописные буквы, строчные буквы, цифры, спецсимволы' 
       });
     }
     
     user.passwordHash = hashPasswordScrypt(newPassword);
     
     // Log password change for audit trail
     auditLog('profile_password_changed', userId, {});
   }
   
   users[idx] = user;
   saveUsers(users);
   
   res.json({ success: true, username: user.username });
});

app.get('/api/user', async (req, res) => {
  const userId = getSessionUserId(req);
  if (!userId) return res.status(401).json({ error: 'Требуется авторизация' });
  
  const users = loadUsers();
  const user = users.find(u => u.id === userId);
  if (!user) return res.status(404).json({ error: 'Пользователь не найден' });
  
  const payload = {
    id: user.id,
    username: user.username,
    twoFactorEnabled: !!user.totpSecret,
    twoFactorPending: !!user.totpPendingSecret
  };
  
  if (user.totpPendingSecret) {
    const otpauth = generateTOTPUri(user.totpPendingSecret, user.username);
    try {
      payload.pending2faQr = await QRCode.toDataURL(otpauth);
    } catch (e) {
      console.error('QR 2FA:', e);
    }
  }
  
  res.json(payload);
});

const server = app.listen(PORT, HOST, () => {
  const displayHost = HOST === '0.0.0.0' ? 'localhost' : HOST;
  console.log(`Сервер WebSSH: http://${displayHost}:${PORT}`);
});

server.on('error', (err) => {
  console.error('HTTP listen error:', err);
});

const wss = new WebSocket.Server({ server, path: '/ws' });
wss.on('error', (err) => {
  console.error('WebSocket server error:', err);
});

const WS_MAX_CONNECTIONS_PER_USER = 5;
const WS_MAX_MESSAGES_PER_MINUTE = 1000;

wss.on('connection', (ws, req) => {
  const userId = getSessionUserId(req);
  if (!userId) {
    try { ws.close(1008, 'auth required'); } catch (_) {}
    return;
  }

  // Проверить количество соединений от пользователя
  const userConnections = Array.from(wss.clients).filter(client => {
    const clientUserId = getSessionUserId(client.upgradeReq || { headers: { cookie: client.headers?.cookie || '' } });
    return clientUserId === userId;
  }).length;
  
  if (userConnections > WS_MAX_CONNECTIONS_PER_USER) {
    ws.close(1008, 'too many connections');
    return;
  }

   // ✓ HIGH #6 + MEDIUM #18: Strengthen WebSocket origin validation
   const origin = req.headers.origin;
   if (origin) {
     try {
       const o = new URL(origin);
       const host = (req.headers.host || '').split(',')[0].trim();
       const protocol = req.headers['x-forwarded-proto'] || (req.connection.encrypted ? 'https' : 'http');
       
       // Validate both protocol and host (prevent CSWSH)
       const expectedProtocol = protocol === 'https' ? 'https:' : 'http:';
       if (o.protocol !== expectedProtocol || o.host !== host) {
         ws.close(1008, 'bad origin');
         return;
       }
     } catch (_) {
       ws.close(1008, 'bad origin');
       return;
     }
   } else if (process.env.NODE_ENV === 'production') {
     // Require origin header in production for CSWSH protection
     ws.close(1008, 'origin required');
     return;
   }

   // Rate limiting для сообщений
   let messageCount = 0;
   let resetTime = Date.now() + 60000;
   // ✓ MEDIUM #12: Add WebSocket message size validation
   const MAX_MESSAGE_SIZE = 1024 * 1024;  // 1MB per message
   const MAX_BUFFER_SIZE = 10 * 1024 * 1024;  // 10MB total per connection
   let totalBufferSize = 0;

  const client = new Client();
  let sshStream = null;

   ws.on('message', (message) => {
     // ✓ MEDIUM #12: Check message size first
     if (message.length > MAX_MESSAGE_SIZE) {
       try { ws.send(JSON.stringify({ type: 'error', message: 'Message too large' })); } catch (_) {}
       ws.close(1008, 'message too large');
       return;
     }
     
     totalBufferSize += message.length;
     if (totalBufferSize > MAX_BUFFER_SIZE) {
       try { ws.send(JSON.stringify({ type: 'error', message: 'Buffer exceeded' })); } catch (_) {}
       ws.close(1008, 'buffer exceeded');
       return;
     }
     
     // Rate limiting
     if (Date.now() > resetTime) {
       messageCount = 0;
       totalBufferSize = 0;
       resetTime = Date.now() + 60000;
     }
     
     messageCount++;
     if (messageCount > WS_MAX_MESSAGES_PER_MINUTE) {
       ws.close(1008, 'rate limit exceeded');
       return;
     }
     
     try {
       const data = JSON.parse(message);
      
      if (data.type === 'connect') {
        const { connectionId } = data;
        if (!connectionId) {
          ws.send(JSON.stringify({ type: 'error', message: 'Missing connectionId' }));
          return;
        }

        const connections = loadConnections(userId);
        const conn = connections.find((c) => c && c.id === connectionId);
        if (!conn) {
          ws.send(JSON.stringify({ type: 'error', message: 'Connection not found' }));
          auditLog('ssh_connection_failed', userId, { connectionId, reason: 'not_found' });
          return;
        }
        
        // Проверить что host разрешён
        if (!isAllowedSshHost(conn.host)) {
          ws.send(JSON.stringify({ type: 'error', message: 'Host not allowed' }));
          auditLog('ssh_connection_blocked', userId, { host: conn.host, reason: 'host_not_allowed' });
          return;
        }
        
        // Проверить порт
        if (!isValidPort(conn.port)) {
          ws.send(JSON.stringify({ type: 'error', message: 'Invalid port' }));
          return;
        }
        
        const connectConfig = {
          host: conn.host,
          port: conn.port || 22,
          username: conn.username,
          readyTimeout: 10000
        };

        if (conn.authType === 'key') {
          const privateKey = decryptSecret(conn.privateKeyEnc);
          if (!privateKey) {
            ws.send(JSON.stringify({ type: 'error', message: 'Private key not configured' }));
            return;
          }
          connectConfig.privateKey = privateKey;
        } else {
          const password = decryptSecret(conn.passwordEnc);
          if (!password) {
            ws.send(JSON.stringify({ type: 'error', message: 'Для этого подключения не задан пароль' }));
            return;
          }
          connectConfig.password = password;
        }

        client.connect(connectConfig);
      } 
      else if (data.type === 'data' && sshStream) {
        sshStream.write(data.data);
      }
      else if (data.type === 'resize' && sshStream) {
        sshStream.setWindow(data.rows, data.cols, data.height, data.width);
      }
      else if (data.type === 'disconnect') {
        sshStream?.end();
        client.end();
      }
    } catch (e) {
      console.error('Ошибка обработки сообщения:', e);
    }
  });

  client.on('ready', () => {
    ws.send(JSON.stringify({ type: 'ready' }));
    
    client.shell({ term: 'xterm-256color' }, (err, stream) => {
      if (err) {
        ws.send(JSON.stringify({ type: 'error', message: err.message }));
        return;
      }

      sshStream = stream;
      
      stream.on('data', (data) => {
        ws.send(JSON.stringify({ type: 'data', data: data.toString('utf8') }));
      });

      stream.on('close', () => {
        ws.send(JSON.stringify({ type: 'close' }));
        client.end();
      });
    });
  });

  client.on('error', (err) => {
    ws.send(JSON.stringify({ type: 'error', message: err.message }));
  });

  ws.on('close', () => {
    sshStream?.end();
    client.end();
  });
});
