import { BrowserRouter, Routes, Route } from 'react-router-dom';
import Dashboard from './components/Dashboard/Dashboard';
import MinedSharesExplorer from './components/BeadsTab/MinedSharesExplorer';
import Footer from './components/Footer/Footer';
import ErrorBoundary from './components/common/ErrorBoundary';

function App() {
  return (
    <div className="min-h-screen flex flex-col bg-[#121212] w-full">
      <BrowserRouter>
        <main className="flex-grow flex flex-col">
          {/* ErrorBoundary wraps each route to catch rendering errors in any page */}
          <Routes>
            <Route
              path="/"
              element={
                <ErrorBoundary>
                  <Dashboard />
                </ErrorBoundary>
              }
            />
            <Route
              path="/minedsharesexplorer"
              element={
                <ErrorBoundary>
                  <MinedSharesExplorer />
                </ErrorBoundary>
              }
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
