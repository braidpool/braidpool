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

#ifndef BP_RUNNER_HPP
#define BP_RUNNER_HPP

#include <boost/asio.hpp>
#include <boost/core/noncopyable.hpp>
#include <boost/thread.hpp>

namespace bp {

using io_context = boost::asio::io_context;

class runner : private boost::noncopyable {
 public:
  void start();
  void stop();
  io_context& get_io_context() { return io_context_; };

 private:
  io_context io_context_;
  // thread group to run io_context
  boost::thread_group threads_;
};

}  // namespace bp

#endif
