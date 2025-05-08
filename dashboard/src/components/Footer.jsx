import { FaGithub, FaTwitter, FaDiscord, FaCode } from 'react-icons/fa';

import { motion } from 'framer-motion';

export default function Footer() {
  return (
    <footer className=" text-gray-300 px-6 sm:px-10 md:px-20 py-8 ml-42 overflow-x-hidden">
      <motion.div
        initial="hidden"
        whileInView="visible"
        viewport={{ once: true }}
        transition={{ staggerChildren: 0.2 }}
        variants={{
          hidden: {},
          visible: {},
        }}
        className="max-w-6xl mx-auto grid grid-cols-5 sm:grid-cols-2 md:grid-cols-4 gap-10"
      >
        {/* Logo & Description */}
        <motion.div
          variants={{
            hidden: { opacity: 0, y: 20 },
            visible: { opacity: 1, y: 0 },
          }}
          className="space-y-3"
        >
          <div className="flex items-center gap-3">
            <motion.img
              whileHover={{ rotate: 12, scale: 1.1 }}
              transition={{ type: 'spring', stiffness: 300 }}
              src="./favicon.ico"
              alt="Braidpool Logo"
              className="h-10 w-10"
            />
            <h1 className="text-xl font-bold text-white tracking-wide">
              Braidpool
            </h1>
          </div>
          <p className="text-sm text-white leading-relaxed mr-7">
            A fully decentralized Bitcoin mining protocol.
            <br />
            Miner-owned. Censorship-resistant. Open-source.
          </p>
        </motion.div>

        {/* Project */}
        <motion.div
          variants={{
            hidden: { opacity: 0, y: 20 },
            visible: { opacity: 1, y: 0 },
          }}
        >
          <h2 className="text-base font-semibold text-white mb-2 mt-2">
            Project
          </h2>
          <ul className="space-y-1 text-sm">
            {['About', 'Documentation', 'Contribute', 'FAQs'].map((item) => (
              <li key={item}>
                <a
                  href={`/${item.toLowerCase()}`}
                  className="hover:text-white hover:translate-x-1 transition-all duration-200 inline-block"
                >
                  {item}
                </a>
              </li>
            ))}
          </ul>
        </motion.div>

        {/* Community */}
        <motion.div
          variants={{
            hidden: { opacity: 0, y: 20 },
            visible: { opacity: 1, y: 0 },
          }}
        >
          <h2 className="text-base font-semibold text-white mb-2 mt-2">
            Community
          </h2>
          <ul className="space-y-2 text-sm">
            <li className="flex items-center gap-2 group">
              <FaGithub className="group-hover:rotate-[360deg] transition-transform duration-500" />
              <a
                href="https://github.com/braidpool/braidpool"
                target="_blank"
                rel="noreferrer"
                className="hover:text-white"
              >
                GitHub
              </a>
            </li>
            <li className="flex items-center gap-2 group">
              <FaTwitter className="group-hover:rotate-[360deg] transition-transform duration-500" />
              <a
                href="https://twitter.com/braidpool"
                target="_blank"
                rel="noreferrer"
                className="hover:text-white"
              >
                Twitter
              </a>
            </li>
            <li className="flex items-center gap-2 group">
              <FaDiscord className="group-hover:rotate-[360deg] transition-transform duration-500" />
              <a href="/forum" className="hover:text-white">
                Discord
              </a>
            </li>
          </ul>
        </motion.div>

        {/* Legal */}
        <motion.div
          variants={{
            hidden: { opacity: 0, y: 20 },
            visible: { opacity: 1, y: 0 },
          }}
        >
          <h2 className="text-base font-semibold text-white mb-2 mt-2">
            Legal
          </h2>
          <ul className="space-y-1 text-sm">
            {[
              ['MIT License', '/license'],
              ['Terms of Use', '/terms'],
              ['Privacy Policy', '/privacy'],
            ].map(([label, link]) => (
              <li key={label}>
                <a
                  href={link}
                  className="hover:text-white hover:translate-x-1 transition-all duration-200 inline-block"
                >
                  {label}
                </a>
              </li>
            ))}
          </ul>
          <ul>
            <li>
              <a
                href="#"
                className="text-gray-400 hover:text-white transition-colors duration-200 flex items-center"
              >
                <FaCode className="h-4 w-4 mr-2" />
                <span>Developer Forum</span>
              </a>
            </li>
          </ul>
        </motion.div>
        <div>
          <h3 className="text-white font-bold mb-4 text-lg">Stay Updated</h3>
          <p className="text-gray-400 mb-4 text-sm">
            Subscribe to our newsletter for the latest updates and insights.
          </p>
          <div className="flex">
            <input
              type="email"
              placeholder="Your email"
              className="bg-gray-900/80 border border-gray-700/80 rounded-l-lg p-2 text-sm flex-grow focus:outline-none focus:border-gray-500"
            />
            <button className="bg-gray-900 hover:bg-gray-600 text-white px-2 rounded-r-lg transition-colors duration-200">
              Subscribe
            </button>
          </div>
        </div>
      </motion.div>

      {/* Bottom Bar */}
      <div className="border-t border-gray-800 mt-8 pt-4 text-center text-xs text-gray-500">
        &copy; {new Date().getFullYear()} Braidpool. Empowering decentralized
        mining.
      </div>
    </footer>
  );
}
