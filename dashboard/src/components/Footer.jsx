export default function Footer() {
  return (
    <footer className="bg-[#1A1A1A] text-gray-300 py-12 px-6 md:px-34 ml-60">
      <div className="max-w-4xl mx-auto grid md:grid-cols-4 gap-10 ">
        {/* Logo and Intro */}
        <div>
          <h1 className="text-2xl font-bold text-white mb-3">Braidpool</h1>
          <p className="text-sm text-gray-400">
            A fully decentralized Bitcoin mining protocol. Miner-owned.
            Censorship-resistant. Open-source.
          </p>
        </div>

        {/* Project Links */}
        <div>
          <h2 className="text-lg font-semibold text-white mb-2">Project</h2>
          <ul className="space-y-1 text-sm">
            <li>
              <a href="/about" className="hover:text-white transition">
                About
              </a>
            </li>
            <li>
              <a href="/docs" className="hover:text-white transition">
                Documentation
              </a>
            </li>
            <li>
              <a href="/contribute" className="hover:text-white transition">
                Contribute
              </a>
            </li>
            <li>
              <a href="/faq" className="hover:text-white transition">
                FAQs
              </a>
            </li>
          </ul>
        </div>

        {/* Community Links */}
        <div>
          <h2 className="text-lg font-semibold text-white mb-2">Community</h2>
          <ul className="space-y-1 text-sm">
            <li>
              <a
                href="https://github.com/braidpool/braidpool"
                target="_blank"
                rel="noreferrer"
                className="hover:text-white transition"
              >
                GitHub
              </a>
            </li>
            <li>
              <a
                href="https://twitter.com/braidpool"
                target="_blank"
                rel="noreferrer"
                className="hover:text-white transition"
              >
                Twitter
              </a>
            </li>
            <li>
              <a href="/forum" className="hover:text-white transition">
                Forum
              </a>
            </li>
          </ul>
        </div>

        {/* Legal Info */}
        <div>
          <h2 className="text-lg font-semibold text-white mb-2">Legal</h2>
          <ul className="space-y-1 text-sm">
            <li>
              <a href="/license" className="hover:text-white transition">
                MIT License
              </a>
            </li>
            <li>
              <a href="/terms" className="hover:text-white transition">
                Terms of Use
              </a>
            </li>
            <li>
              <a href="/privacy" className="hover:text-white transition">
                Privacy Policy
              </a>
            </li>
          </ul>
        </div>
      </div>

      {/* Bottom Bar */}
      <div className="border-t border-gray-800 mt-12 pt-6 text-center text-sm text-gray-500">
        &copy; {new Date().getFullYear()} Braidpool. Empowering decentralized
        mining.
      </div>
    </footer>
  );
}
