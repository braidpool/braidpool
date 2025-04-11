import { cn } from "@/lib/utils";

const Navbar = ({
  active,
  setActive,
}: {
  active: string;
  setActive: (item: string) => void;
}) => {

  const navItems = ["BraidPool", "Bitcoin Stats", "Mining Stats"];

  return (
    <nav className="bg-[#0077B6] dark:bg-[#023E8A] shadow-md p-4 fixed top-0 left-0 w-full z-50">
      <div className="max-w-6xl mx-auto flex justify-between items-center">
        <h1 className="text-xl font-bold text-white dark:text-white">BraidPool Dashboard</h1>
        <ul className="flex space-x-6">
          {navItems.map((item) => (
            <li
              key={item}
              className={cn(
                "cursor-pointer px-3 py-2 rounded-lg transition",
                active === item
                  ? "bg-[#FF8500] dark:bg-[#E76F00] text-white font-semibold"
                  : "hover:bg-[#48CAE4] dark:hover:bg-[#0096C7] text-white dark:text-white"
              )}
              onClick={() => setActive(item)}
            >
              {item}
            </li>
          ))}
        </ul>
      </div>
    </nav>
  );
};

export default Navbar;