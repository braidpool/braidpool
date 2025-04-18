import { motion, AnimatePresence } from "framer-motion";

export default function Particles() {
  return (
    <>
      {Array.from({ length: 15 }).map((_, i) => (
        <Particle key={i} delay={i * 0.5} />
      ))}
    </>
  );
}

function Particle({ delay = 0 }: { delay?: number }) {
  const randomX = Math.random() * 100;
  const randomSize = Math.random() * 3 + 1;
  const randomDuration = Math.random() * 10 + 15;
  const randomOpacity = Math.random() * 0.5 + 0.1;

  return (
    <motion.div
      className="absolute rounded-full bg-blue-500"
      style={{
        left: `${randomX}%`,
        width: `${randomSize}px`,
        height: `${randomSize}px`,
        opacity: 0,
      }}
      initial={{ y: "110vh", opacity: 0 }}
      animate={{
        y: "-10vh",
        opacity: [0, randomOpacity, 0],
      }}
      transition={{
        duration: randomDuration,
        repeat: Number.POSITIVE_INFINITY,
        delay: delay,
        ease: "linear",
      }}
    />
  );
}
