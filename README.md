# WebSSH - Terminal in Your Browser

A lightweight, secure SSH client that runs entirely in your browser. No installation needed. No downloads. Just open and connect.

## Features

✨ **Browser-based** - Works anywhere: desktop, tablet, mobile  
🔐 **Secure** - Your credentials never leave your device  
⚡ **Lightweight** - Fast, minimal dependencies  
🎨 **Clean UI** - Simple and intuitive interface  
📱 **Responsive** - Works on any screen size  
🔌 **No Installation** - Just open the link and connect  

## Use Cases

- Quick SSH connections without installing PuTTY/Terminal
- Remote server management from tablets/phones
- Teaching/demos without setup hassle
- DevOps engineers who need fast SSH access anywhere
- Accessing servers from restricted networks (some firewalls allow WebSocket)

## How It Works

1. Go to [webssh.su](https://webssh.su)
2. Enter your SSH credentials (host, username, password/key)
3. Connect and use terminal in browser
4. Everything runs client-side - we don't store your data

## Security

- No server-side logging of commands or passwords
- All communication is encrypted
- Source code is open for audit
- Your credentials stay in your browser session

## Installation (Self-hosted)
```bash
git clone https://github.com/yourusername/webssh
cd webssh
npm install
npm start
```

## Tech Stack

- Frontend: [Your framework - React/Vue/Vanilla JS]
- WebSocket for SSH tunneling
- [SSH library you're using]

## Roadmap

- [ ] Session history & saved connections
- [ ] Multi-tab support
- [ ] SSH key management
- [ ] Dark mode
- [ ] Team/Enterprise features

## Contributing

Found a bug? Have an idea? Open an issue or PR!

## License

This project is licensed under the **GNU Affero General Public License v3.0**

See [LICENSE](LICENSE) for details.

**In short:** If you use this code to provide a service, you must release your source code.
