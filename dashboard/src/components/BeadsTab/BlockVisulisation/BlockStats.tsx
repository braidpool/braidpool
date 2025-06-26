import { Activity, Layers, Database, Clock } from 'lucide-react';
import AnimatedStatCard from '../AnimatedStatCard';
export function BlockStats() {
  return (
    <div className="grid grid-cols-1 md:grid-cols-4 gap-4 mt-6">
      <AnimatedStatCard
        title="Total Blocks"
        value="8,901"
        change="+15%"
        icon={<Layers />}
        color="blue"
        delay={0.2}
      />
      <AnimatedStatCard
        title="Avg Block Size"
        value="1.2 MB"
        change="+0.2 MB"
        icon={<Database />}
        color="purple"
        delay={0.3}
      />
      <AnimatedStatCard
        title="Avg Block Time"
        value="9.8 min"
        change="-0.3 min"
        icon={<Clock className="h-5 w-5" />}
        color="emerald"
        delay={0.4}
      />
      <AnimatedStatCard
        title="Network Difficulty"
        value="11.4 T"
        change="+5%"
        icon={<Activity />}
        color="amber"
        delay={0.5}
      />
    </div>
  );
}
