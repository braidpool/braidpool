// import { motion, AnimatePresence } from 'framer-motion';
// import { Award, Check, Star, Trophy, Medal, Gift, Zap } from 'lucide-react';
// import { useState } from 'react';

// interface RewardMilestonesProps {
//   achievements: string[];
// }

// export function RewardMilestones({ achievements = [] }: RewardMilestonesProps) {
//   const [selectedAchievement, setSelectedAchievement] = useState<string | null>(
//     null
//   );

//   // Filter achievements based on what the user has earned
//   // const earnedAchievements = allAchievements.filter((a) =>
//   //   achievements.includes(a.id)
//   // );
//   // const lockedAchievements = allAchievements.filter(
//   //   (a) => !achievements.includes(a.id)
//   // );

//   return (
//     <div className="space-y-8 bg-black w-full rounded-xl p-6">
//       {/* Earned achievements */}
//       <div>
//         <h3 className="text-xl font-bold text-white mb-4 flex items-center">
//           <Trophy className="h-6 w-6 text-amber-400 mr-2" />
//           Earned Achievements
//         </h3>

//         <div className="grid grid-cols-4 sm:grid-cols-2 md:grid-cols-3 gap-4">
//           {earnedAchievements.map((achievement, index) => (
//             <motion.div
//               key={achievement.id}
//               className={`relative border border-gray-800/50 rounded-xl p-4 bg-black  overflow-hidden cursor-pointer`}
//               initial={{ opacity: 0, y: 20 }}
//               animate={{ opacity: 1, y: 0 }}
//               transition={{ duration: 0.4, delay: index * 0.1 }}
//               whileHover={{ scale: 1.02, y: -5 }}
//               onClick={() =>
//                 setSelectedAchievement(
//                   achievement.id === selectedAchievement ? null : achievement.id
//                 )
//               }
//             >
//               {/* Animated border gradient */}
//               <div className="absolute inset-0 p-[1px] rounded-xl overflow-hidden pointer-events-none">
//                 <motion.div
//                   className={`absolute inset-0 `}
//                   animate={{
//                     backgroundPosition: ['0% 0%', '200% 0%'],
//                   }}
//                   transition={{
//                     duration: 8,
//                     repeat: Number.POSITIVE_INFINITY,
//                     repeatType: 'loop',
//                     ease: 'linear',
//                   }}
//                 />
//               </div>

//               <div className="flex items-start justify-between">
//                 <div className="flex items-center">
//                   <div className="p-2 rounded-lg bg-gray-900/50">
//                     {achievement.icon}
//                   </div>
//                   <div className="ml-3">
//                     <h4 className="font-bold text-white">
//                       {achievement.title}
//                     </h4>
//                     <p className="text-gray-400 text-sm mt-1">
//                       {achievement.description}
//                     </p>
//                   </div>
//                 </div>
//                 <div className="bg-gray-900/50 p-1 rounded-full">
//                   <Check className="h-4 w-4 text-green-400" />
//                 </div>
//               </div>

//               <div className="mt-4 text-right">
//                 <span className="text-xs text-gray-500">
//                   Earned on {achievement.date}
//                 </span>
//               </div>

//               {/* Expanded details */}
//               <AnimatePresence>
//                 {selectedAchievement === achievement.id && (
//                   <motion.div
//                     initial={{ height: 0, opacity: 0 }}
//                     animate={{ height: 'auto', opacity: 1 }}
//                     exit={{ height: 0, opacity: 0 }}
//                     transition={{ duration: 0.3 }}
//                     className="mt-4 pt-4 border-t border-gray-800/50 overflow-hidden"
//                   >
//                     <p className="text-sm text-gray-300">
//                       Congratulations on earning this achievement! This
//                       milestone represents significant progress in your mining
//                       journey.
//                     </p>
//                   </motion.div>
//                 )}
//               </AnimatePresence>
//             </motion.div>
//           ))}
//         </div>
//       </div>

//       {/* Locked achievements */}
//       <div>
//         <h3 className="text-xl font-bold text-white mb-4 flex items-center">
//           <Award className="h-6 w-6 text-gray-400 mr-2" />
//           Upcoming Achievements
//         </h3>

//         <div className="grid grid-cols-2 sm:grid-cols-2 md:grid-cols-3 gap-4">
//           {lockedAchievements.map((achievement, index) => (
//             <motion.div
//               key={achievement.id}
//               className="relative border border-gray-800/50 rounded-xl p-4 bg-gray-900/30 backdrop-blur-md overflow-hidden"
//               initial={{ opacity: 0, y: 20 }}
//               animate={{ opacity: 1, y: 0 }}
//               transition={{ duration: 0.4, delay: 0.3 + index * 0.1 }}
//             >
//               <div className="flex items-start justify-between">
//                 <div className="flex items-center">
//                   <div className="p-2 rounded-lg bg-gray-900/50">
//                     {achievement.icon}
//                   </div>
//                   <div className="ml-3">
//                     <h4 className="font-bold text-gray-300">
//                       {achievement.title}
//                     </h4>
//                     <p className="text-gray-500 text-sm mt-1">
//                       {achievement.description}
//                     </p>
//                   </div>
//                 </div>
//               </div>

//               <div className="mt-4 text-right">
//                 <span className="text-xs text-gray-600">Locked</span>
//               </div>
//             </motion.div>
//           ))}
//         </div>
//       </div>
//     </div>
//   );
// }
