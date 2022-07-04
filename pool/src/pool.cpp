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

#include <boost/asio/detached.hpp>

#include "p2p/connection.hpp"
#include "util/log.hpp"
#define pool_VERSION_MAJOR @pool_VERSION_MAJOR @
#define pool_VERSION_MINOR @pool_VERSION_MINOR @

#include <boost/log/trivial.hpp>
#include <iostream>
#include <p2p/node.hpp>

#include "p2p/connection.hpp"
#include "runner.hpp"
#include "system.hpp"

using namespace bp;
using namespace bp::p2p;

using node_t = node<connection>;

int main(int argc, char* argv[]) {
  LOG_INFO << "Starting braid pool...";
  try {
    if (argc != 3 && argc != 5) {
      std::cout << "Usage: bp";
      std::cout << " <listen_address> <listen_port>";
      std::cout << " <peer_address> <peer_port>\n";
      return 1;
    }
  } catch (std::exception& e) {
    LOG_ERROR << e.what();
  }

  runner node_runner;
  // TODO(kp): Improve arg parsing
  std::string listen_address{argv[1]};
  std::string listen_port{argv[2]};
  node_t::connections_mgr mgr{};
  node_t node_(node_runner.get_io_context(), listen_address, listen_port, mgr);

  LOG_INFO << "Node created...";
  node_.start();
  if (argc == 5) {
    std::string peer_address{argv[3]};
    std::string peer_port{argv[4]};
    co_spawn(node_runner.get_io_context(),
             node_.connect_to_peers(peer_address, peer_port),
             boost::asio::detached);
  }
  node_runner.start();
}
