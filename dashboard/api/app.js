import express from 'express';
import cors from 'cors';
import proxyRoute from './routes/proxyRoute.js';

const app = express();

app.use(cors({
  origin: 'http://localhost:3000',
  credentials: true,
}));
app.use(express.json());


app.use('/api', proxyRoute);

export default app;
