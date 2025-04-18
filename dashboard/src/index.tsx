import React from 'react';
import ReactDOM from 'react-dom/client';
import './index.css';
import App from './App';

// For debugging
console.log('🚀 Braidpool Dashboard starting up!');

ReactDOM.createRoot(document.getElementById('root') as HTMLElement).render(
  <React.StrictMode>
    <App />
  </React.StrictMode>
);
