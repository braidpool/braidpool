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

#include "p2p/node.hpp"

#include <gmock/gmock-function-mocker.h>
#include <gmock/gmock-spec-builders.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <sys/socket.h>

#include <boost/asio/awaitable.hpp>
#include <boost/asio/co_spawn.hpp>
#include <boost/asio/detached.hpp>
#include <boost/asio/this_coro.hpp>

#include "p2p/connection.hpp"
#include "p2p/connections_manager.hpp"
#include "p2p/define.hpp"
#include "p2p/node.hpp"
#include "runner.hpp"
#include "util/log.hpp"

namespace bp {
namespace p2p {

using test_node = node<connection>;

TEST(NODE_TEST, CONSTRUCTOR__RETURNS_NODE) {
  test_node::connections_mgr mgr{};
  runner node_runner;
  test_node instance{node_runner.get_io_context(), "localhost", "22142", mgr};

  instance.start();
}

}  // namespace p2p
}  // namespace bp
