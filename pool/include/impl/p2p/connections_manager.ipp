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

#ifndef BP_CONNECTIONS_MANAGER_IPP
#define BP_CONNECTIONS_MANAGER_IPP

#include <algorithm>

#include "p2p/connections_manager.hpp"
#include "system.hpp"

template <typename connection_ptr>
void bp::p2p::connections_manager<connection_ptr>::add_connection(
    connection_ptr con) {
  boost::mutex::scoped_lock lock(connections_mutex_);
  connections_.insert(con);
}

template <typename connection_ptr>
void bp::p2p::connections_manager<connection_ptr>::remove_connection(
    connection_ptr con) {
  boost::mutex::scoped_lock lock(connections_mutex_);
  LOG_DEBUG << "Scoped lock taken...";
  connections_.erase(con);
  LOG_DEBUG << "erased......";
}

#endif
