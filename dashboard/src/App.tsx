import { BrowserRouter, Navigate, Route, Routes } from 'react-router-dom';
import Dashboard from './components/Dashboard/Dashboard';
import Footer from './components/Footer/Footer';
import { useState, useEffect } from 'react';
import { themes, ThemeType } from './theme/colors';

function App() {
  const [currentTheme, setCurrentTheme] = useState<ThemeType>('dark');

  useEffect(() => {
    const themeParams = themes[currentTheme];
    const root = document.documentElement;
    Object.keys(themeParams).forEach((key) => {
      root.style.setProperty(key, themeParams[key]);
    });
  }, [currentTheme]);

  return (
    <div className="min-h-screen flex flex-col bg-background w-full transition-colors duration-300">
      <BrowserRouter>
        <main className="flex-grow flex flex-col">
          <Routes>
            <Route
              path="/"
              element={<Navigate to="/dashboard" replace />}
            />
            <Route
              path="/:page"
              element={
                <Dashboard
                  currentTheme={currentTheme}
                  setCurrentTheme={setCurrentTheme}
                />
              }
            />
            <Route
              path="/minedsharesexplorer"
              element={<Navigate to="/miner-stats" replace />}
            />
          </Routes>
        </main>
        <div className="py-6 mt-6 border-t border-border">
          <Footer />
        </div>
      </BrowserRouter>
    </div>
  );
}

export default App;
