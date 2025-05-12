import { defineConfig } from 'vocs'
import remarkMath from 'remark-math'
import rehypeKatex from 'rehype-katex'

export default defineConfig({
  title: 'Braidpool Documentation',
  rootDir: '.',
  basePath: '/',
  aiCta: true,
  markdown: {
    remarkPlugins: [ 
      remarkMath 
    ],
    rehypePlugins: [
      rehypeKatex
    ]
  },
  topNav: [ 
    { text: 'How to Contribute?', link: '/overview#current-status-and-how-to-contribute', match: '/overview' }, 
    { text: 'Discord', link: 'https://discord.gg/pZYUDwkpPv' }, 
  ], 
  iconUrl: { 
    light: '/icon-light.svg', 
    dark: '/icon-dark.svg'
  }, 
  sidebar: [
    {
      text: 'What is Braidpool?',
      link: '/overview',
      collapsed: true,
      items: [
        {
          text: 'Why?',
          link: '/overview#why',
        },
        {
          text: 'What does Braidpool mean for existing pools?',
          link: '/overview#what-does-braidpool-mean-for-existing-pools',
        },
        {
          text: 'What does Braidpool mean for existing miners?',
          link: '/overview#what-does-braidpool-mean-for-miners',
        },
        {
          text: 'A Few Technical Details',
          link: '/overview#a-few-technical-details',
        },
        {
          text: 'Current Status and How to Contribute',
          link: '/overview#current-status-and-how-to-contribute',
        },
      ],
    },
    {
      text: 'General Considerations',
      link: '/general_considerations',
      collapsed: true,
      items: [
        {
          text: 'Decentralized Mining Pools',
          link: '/general_considerations#decentralized-mining-pools',
        },
        {
          text: 'Weak Blocks',
          link: '/general_considerations#weak-blocks',
        },
        {
          text: 'Consensus Mechanism',
          link: '/general_considerations#consensus-mechanism',
        },
        {
          text: 'Payout Commitment',
          link: '/general_considerations#payout-commitment',
          collapsed: true,
          items: [
            {
              text: 'The Unspent Hasher Payment Output (UHPO) mechanism',
              link: '/general_considerations#the-unspent-hasher-payment-output-uhpo-mechanism',
            },
            {
              text: 'Pool Transactions and Derivative Instruments',
              link: '/general_considerations#pool-transactions-and-derivative-instruments',
            },
          ],
        },

        {
          text: 'Payout Authorization',
          link: '/general_considerations#payout-authorization',
          collapsed: true,
          items: [
            {
              text: 'Schnorr Threshold Signatures',
              link: '/general_considerations#schnorr-threshold-signatures',
            },
          ],
        },        
        {
          text: 'Transaction Selection',
          link: '/general_considerations#transaction-selection',
        },
        {
          text: 'Unsolved Problems and Future Directions',
          link: '/general_considerations#unsolved-problems-and-future-directions',
          collapsed: true,
          items: [
            {
              text: 'Covenants',
              link: '/general_considerations#covenants',
            },
            {
              text: 'Sub-Pools',
              link: '/general_considerations#sub-pools',
            },
          ],
        },
      ],
    },
    {
      text: 'Braidpool Specification',
      link: '/braidpool_spec',
      collapsed: true,
      items: [
        {
          text: 'Shares and Weak Blocks',
          link: '/braidpool_spec#shares-and-weak-blocks',
          collapsed: true,
          items: [
            {
              text: 'Metadata Commitments',
              link: '/braidpool_spec#metadata-commitments',
            },
            {
              text: 'Committed Mempool',
              link: '/braidpool_spec#committed-mempool',
            },
            {
              text: 'Share Value',
              link: '/braidpool_spec#share-value',
            },
          ]
        },
        
        {
          text: 'Braid Consensus Mechanism',
          link: '/braidpool_spec#braid-consensus-mechanism',
          collapsed: true,
          items: [
            {
              text: 'Simple Sum of Descendant Work',
              link: '/braidpool_spec#simple-sum-of-descendant-work',
            },
            {
              text: 'Difficulty Retarget Algorithm',
              link: '/braidpool_spec#difficulty-retarget-algorithm',
            },
            {
              text: 'Miner Selected Difficulty',
              link: '/braidpool_spec#miner-selected-difficulty',
            },
          ]
        },
        {
          text: 'Payout Update',
          link: '/braidpool_spec#payout-update',
          collapsed: true,
          items: [
            {
              text: 'Unspent Hasher Payment Output',
              link: '/braidpool_spec#unspent-hasher-payment-output',
            },
          ]
        },
        {
          text: 'Payout Update and Settlement Signing',
          link: '/braidpool_spec#payout-update-and-settlement-signing',
          collapsed: true,
          items: [
            {
              text: 'Pool Transactions and Derivative Instruments',
              link: '/braidpool_spec#pool-transactions-and-derivative-instruments',
            },
          ]
        },
        {
          text: 'Payout Authorization',
          link: '/braidpool_spec#payout-authorization',
          collapsed: true,
          items: [
            {
              text: 'Schnorr Threshold Signatures',
              link: '/braidpool_spec#schnorr-threshold-signatures',
            },
          ]
        },
        
        {
          text: 'Transaction Selection',
          link: '/braidpool_spec#transaction-selection',
        },
        {
          text: 'Attacks',
          link: '/braidpool_spec#attacks',
          collapsed: true,
          items: [
            {
              text: 'Block Withholding',
              link: '/braidpool_spec#block-withholding',
            },
            {
              text: '51% Attack',
              link: '/braidpool_spec#51-attack',
            }
          ],
        },
        {
          text: 'Active Research and Future Directions',
          link: '/braidpool_spec#active-research-and-future-directions',
          collapsed: true,
          items: [
            {
              text: 'Sub-Pools',
              link: '/braidpool_spec#sub-pools',
            },
          ]
        },
      ],
    },
    {
      text: 'Bitcoin Hashrate Derivatives Trading',
      link: '/derivatives',
      collapsed: true,
      items: [
        {
          text: 'Introduction',
          link: '/derivatives#introduction',
        },
        {
          text: 'Hashrate Derivatives Emulate FPPS',
          link: '/derivatives#hashrate-derivatives-emulate-fpps',
        },
        {
          text: 'Auditing The Miner',
          link: '/derivatives#auditing-the-miner',
        },
        {
          text: 'What Happens Today',
          link: '/derivatives#what-happens-today',
        },
        {
          text: 'The Future',
          link: '/derivatives#the-future',
        },
      ],
    },
    {
      text: 'Braidpool Consensus',
      link: '/braid_consensus',
      collapsed: true,
      items: [
        {
          text: 'Braid Structure',
          link: '/braid_consensus#braid-structure',
        },
        {
          text: 'Braid Mathematics',
          link: '/braid_consensus#braid-mathematics',
        },
        {
          text: 'Consensus',
          link: '/braid_consensus#consensus',
        },
        {
          text: 'Byzantine Broadcast',
          link: '/braid_consensus#byzantine-broadcast',
        },
      ],
    },
    {
      text: 'Roadmap',
      link: '/roadmap',
    },
  ],
  socials: [
    {
      icon: "github",
      link: "https://github.com/braidpool/",
    },
    {
      icon: "x",
      link: "https://x.com/braidpool",
    },
    // {
    //   icon: "telegram",
    //   link: "https://t.me/braidpool",
    // },
  ],
})
