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

#include "runner.hpp"

namespace bp {

void runner::start() {
  // brute force stop context for now.
  boost::asio::signal_set signals(io_context_, SIGINT, SIGTERM);
  signals.async_wait([&](auto, auto) { io_context_.stop(); });

  for (unsigned i = 0; i < boost::thread::hardware_concurrency(); ++i)
    threads_.create_thread(boost::bind(&io_context::run, &io_context_));
  threads_.join_all();
}

void runner::stop() {}

}  // namespace bp
