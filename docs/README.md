# Braidpool Documentation

This is the documentation site for Braidpool, built with [Vocs](https://vocs.dev).

## Getting Started

### Prerequisites

- Node.js 
- npm or yarn

### Installation

```bash
# Install dependencies
npm install
```

### Development

To start the development server:

```bash
npm run dev
```

This will start a local development server at http://localhost:5173 (or another port if 5173 is in use).

### Building for Production

To build the documentation site for production:

```bash
npm run build
```

This will generate static files in the `dist` directory.

### Preview Production Build

To preview the production build locally:

```bash
npm run preview
```

## Project Structure

- `pages/` - Documentation content (Markdown/MDX files)
- `public/` - Static assets
- `vocs.config.ts` - Vocs configuration
