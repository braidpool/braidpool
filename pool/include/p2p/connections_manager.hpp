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

#ifndef BP_CONNECTIONS_MANAGER_HPP
#define BP_CONNECTIONS_MANAGER_HPP

#include <boost/thread/mutex.hpp>
#include <set>

namespace bp {
namespace p2p {

template <typename connection_ptr>
class connections_manager {
 public:
  using connections = std::set<connection_ptr>;

  void add_connection(connection_ptr connection_);
  void remove_connection(connection_ptr connection_);

 private:
  // protects add/remove connections
  boost::mutex connections_mutex_;

  // protected by connections_mutex_
  connections connections_;
};
}  // namespace p2p
}  // namespace bp

#include "impl/p2p/connections_manager.ipp"

#endif
