import { StrictMode } from 'react'
import { createRoot } from 'react-dom/client'
import './index.css'
import GraphVisualization from './BraidPoolGraph/BraidPoolGraph.tsx'
import Navbar from './Navbar/Navbar.tsx'

createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <Navbar />
    <GraphVisualization />
  </StrictMode>,
)
