import { StrictMode, useState } from "react";
import { createRoot } from "react-dom/client";
import "./index.css";
import GraphVisualization from "./BraidPoolGraph/BraidPoolGraph.tsx";
import Navbar from "./Navbar/Navbar.tsx";
import { MiningStats } from "./MiningStats/MiningStats.tsx";
import { BitcoinStats } from "./BitcoinStats/BitcoinStats.tsx";

const App = () => {
  const [active, setActive] = useState("BraidPool");

  const renderComponent = () => {
    switch (active) {
      case "BraidPool":
        return <GraphVisualization />;
      case "Bitcoin Stats":
        return <BitcoinStats />;
      case "Mining Stats":
        return <MiningStats />;
      default:
        return <GraphVisualization />;
    }
  };

  return (
    <StrictMode>
      <Navbar active={active} setActive={setActive} />
      <div className="container mx-auto mt-4 p-4">{renderComponent()}</div>
    </StrictMode>
  );
};

createRoot(document.getElementById("root")!).render(<App />);
