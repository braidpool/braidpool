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

#include <boost/asio/io_context.hpp>
#include <boost/thread.hpp>
#include <iostream>
#include <p2p/define.hpp>

#include "system.hpp"
#include "util/log.hpp"

using boost::asio::awaitable;
using boost::asio::co_spawn;
using boost::asio::detached;
using boost::asio::io_context;
using boost::asio::use_awaitable;

namespace bp {
namespace p2p {

node::node(io_context& ctx, const std::string& listen_address,
           const std::string& listen_port)
    : ctx_(ctx) {
  auto listen_endpoint = *tcp::resolver(ctx_).resolve(
      listen_address, listen_port, tcp::resolver::passive);
  acceptor_ = std::make_unique<tcp::acceptor>(ctx_, listen_endpoint);
}

node::~node() {
  std::cerr << "Stopping node..." << std::endl;
  this->stop();
  std::cerr << "Node stopped." << std::endl;
}

// TODO: guard against duplicate connection creation to the same
// peer. One in response to incoming connection other via this call.
awaitable<void> node::connect_to_peers(const std::string& host,
                                       const std::string& port) {
  auto peer_endpoint = *tcp::resolver(ctx_).resolve(host, port);
  auto client_socket = tcp::socket(ctx_);
  std::cerr << "Calling connect..." << std::endl;
  co_await client_socket.async_connect(peer_endpoint, use_awaitable);
  std::cerr << "Connect returned..." << std::endl;
  co_spawn(ctx_, start_connection(std::move(client_socket)), detached);
}

awaitable<void> node::listen(tcp::acceptor& acceptor) {
  std::cerr << "Listening..." << std::endl;
  for (;;) {
    auto client = co_await acceptor.async_accept(use_awaitable);
    std::cerr << "Accept returned..." << std::endl;
    auto client_executor = client.get_executor();
    co_spawn(client_executor, start_connection(std::move(client)), detached);
  }
}

awaitable<void> node::start_connection(tcp::socket client) {
  std::cerr << "Start connection..." << std::endl;
  auto client_connection = std::make_shared<connection>(std::move(client));
  auto ex = client.get_executor();
  std::cerr << "calling receive..." << std::endl;
  co_spawn(ex, client_connection->receive_from_peer(), detached);
  boost::asio::steady_timer timer_{ex};
  boost::system::error_code ec;
  for (;;) {
    co_await client_connection->send_to_peer("ping\r\n");
    timer_.expires_after(std::chrono::seconds(5));
    co_await timer_.async_wait(redirect_error(use_awaitable, ec));
  }
}

void node::start(const std::string& peer_host, const std::string& peer_port) {
  std::cerr << "In start..." << std::endl;
  co_spawn(ctx_, listen(*acceptor_), detached);
  co_spawn(ctx_, connect_to_peers(peer_host, peer_port), detached);
}

void node::stop() {}

// void node::add_connection(connection& con)
// {
//     connections_mutex_.lock();
//     connections_.insert(con);
//     connections_mutex_.unlock();
// }

// void node::remove_connection(connection& con)
// {
//     connections_mutex_.lock();
//     connections_.erase(con);

//     connections_mutex_.unlock();
// }

}  // namespace p2p
}  // namespace bp
