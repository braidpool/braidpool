import { BrowserRouter, Routes, Route } from 'react-router-dom';
import Dashboard from './components/Dashboard/Dashboard';
import MinedSharesExplorer from './components/BeadsTab/MinedSharesExplorer';
import Footer from './components/Footer';

function App() {
  return (
    <div className="min-h-screen flex flex-col bg-[#121212] w-full">
      <BrowserRouter>
        <main className="flex-grow flex flex-col">
          <Routes>
            <Route path="/" element={<Dashboard />} />
            <Route
              path="/minedsharesexplorer"
              element={<MinedSharesExplorer />}
            />
          </Routes>
        </main>
        <footer className="py-6 mt-6 bg-[#1e1e1e] border-t border-white/10">
          <Footer />
        </footer>
      </BrowserRouter>
    </div>
  );
}

export default App;
