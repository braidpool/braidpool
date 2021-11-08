/**
 * Copyright (c) 2021 braidpool developers (see AUTHORS)
 *
 * This file is part of braidpool.
 *
 * braidpool is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * braidpool is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with braidpool.  If not, see <https://www.gnu.org/licenses/>.
 */

#ifndef BP_SPIN_LOCK_HPP
#define BP_SPIN_LOCK_HPP

#include <boost/atomic.hpp>
#include <memory>

namespace bp {

class spinlock {
public:
    spinlock()
        : state_(unlocked)
    {
    }

    void lock()
    {
        while (state_.exchange(locked, boost::memory_order_acquire) == locked) {
            /* busy-wait */
        }
    }
    void unlock() { state_.store(unlocked, boost::memory_order_release); }

private:
    typedef enum { locked, unlocked } lockstate;
    boost::atomic<lockstate> state_;
};

class scopedspinlock {
public:
    scopedspinlock(std::shared_ptr<spinlock> lock)
        : spinlock_(lock)
    {
        spinlock_->lock();
    }

    ~scopedspinlock() { spinlock_->unlock(); }

    scopedspinlock(const scopedspinlock&) = delete;
    scopedspinlock& operator=(const scopedspinlock&) = delete;
    scopedspinlock(scopedspinlock&&) = delete;
    scopedspinlock& operator=(scopedspinlock&&) = delete;

private:
    std::shared_ptr<spinlock> spinlock_;
};

}

#endif
