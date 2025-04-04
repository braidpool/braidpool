import { ReloadIcon } from '@radix-ui/react-icons';
import { useState } from 'react'

export const MiningStats = () => {
    const [loading, setLoading] = useState(true);

    if (loading) {
        return (
            <div className="fixed inset-0 flex items-center justify-center">
                <div className="flex flex-col items-center">
                    <ReloadIcon className="h-8 w-8 animate-spin text-[#FF8500]" />
                    <p className="mt-4 text-[#0077B6]">Loading Mining Data...</p>
                </div>
            </div>
        );
    }
}
