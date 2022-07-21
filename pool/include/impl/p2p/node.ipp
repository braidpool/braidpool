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

#ifndef BP_NODE_IPP
#define BP_NODE_IPP

#include <boost/asio/detached.hpp>
#include <boost/asio/io_context.hpp>
#include <boost/thread.hpp>
#include <boost/thread/pthread/mutex.hpp>
#include <iostream>
#include <memory>
#include <p2p/define.hpp>

#include "p2p/node.hpp"
#include "system.hpp"
#include "util/log.hpp"

using boost::asio::awaitable;
using boost::asio::co_spawn;
using boost::asio::detached;
using boost::asio::use_awaitable;

namespace bp {
namespace p2p {

template <typename connection_t>
node<connection_t>::node(io_context& ctx, const std::string& listen_address,
                         const std::string& listen_port)
    : ctx_(ctx) {
  auto listen_endpoint = *tcp::resolver(ctx_).resolve(
      listen_address, listen_port, tcp::resolver::passive);
  acceptor_ = std::make_unique<tcp::acceptor>(ctx_, listen_endpoint);
}

template <typename connection_t>
node<connection_t>::~node() {
  LOG_INFO << "Stopping node..." << this;
  this->stop();
  LOG_INFO << "Node stopped." << this;
}

// TODO: guard against duplicate connection creation to the same
// peer. One in response to incoming connection other via this call.
template <typename connection_t>
awaitable<void> node<connection_t>::connect_to_peers(const std::string& host,
                                                     const std::string& port) {
  auto peer_endpoint = *tcp::resolver(ctx_).resolve(host, port);
  auto client_socket = tcp::socket(ctx_);
  co_await client_socket.async_connect(peer_endpoint, use_awaitable);
  auto client_connection =
      std::make_shared<connection_t>(std::move(client_socket));
  connections_mgr_.add_connection(client_connection);
  client_connection->start();
  co_spawn(client_connection->get_socket().get_executor(),
           shares_protocol{client_connection}.start_handshake(), detached);

  LOG_DEBUG << "After start...";
}

template <typename connection_t>
awaitable<void> node<connection_t>::listen(tcp::acceptor& acceptor) {
  LOG_DEBUG << "Listening...";
  for (;;) {
    auto client = co_await acceptor.async_accept(use_awaitable);
    LOG_DEBUG << "Accept returned...";
    auto client_executor = client.get_executor();
    auto client_connection = std::make_shared<connection_t>(std::move(client));
    connections_mgr_.add_connection(client_connection);
    client_connection->start();
    LOG_DEBUG << "After accept and start...";
  }
}

template <typename connection_t>
void node<connection_t>::start() {
  LOG_DEBUG << "In start...";
  co_spawn(ctx_, listen(*acceptor_), detached);
}

template <typename connection_t>
void node<connection_t>::stop() {
  ctx_.stop();
}

}  // namespace p2p
}  // namespace bp

#endif
