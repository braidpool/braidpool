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

#ifndef BP_P2P_PROTOCOL_IPP
#define BP_P2P_PROTOCOL_IPP

#include <boost/asio/awaitable.hpp>
#include <boost/asio/detached.hpp>
#include <boost/thread.hpp>
#include <iostream>
#include <p2p/define.hpp>

#include "p2p/protocol.hpp"
#include "system.hpp"
#include "util/log.hpp"

using boost::asio::awaitable;
using boost::asio::use_awaitable;

namespace bp {
namespace p2p {

template <typename connection_ptr>
protocol<connection_ptr>::protocol(connection_ptr connection)
    : connection_(connection) {}

template <typename connection_ptr>
awaitable<void> protocol<connection_ptr>::start_handshake() {
  boost::asio::steady_timer timer_{connection_->get_socket().get_executor()};
  boost::system::error_code ec;
  for (;;) {
    co_await connection_->send_to_peer("ping\r\n");
    timer_.expires_after(std::chrono::seconds(5));
    co_await timer_.async_wait(redirect_error(use_awaitable, ec));
  }
}

}  // namespace p2p
}  // namespace bp

#endif
