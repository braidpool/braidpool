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

#ifndef BP_NODE_HPP
#define BP_NODE_HPP

#include <boost/core/noncopyable.hpp>
#include <boost/thread.hpp>
#include <boost/thread/mutex.hpp>
#include <p2p/connection.hpp>
#include <p2p/define.hpp>
#include <set>

namespace bp {
namespace p2p {
class node : private boost::noncopyable {
 public:
  node(const std::string& listen_address, const std::string& listen_port);
  ~node();
  awaitable<void> connect_to_peers(const std::string& host,
                                   const std::string& port);
  awaitable<void> listen(tcp::acceptor& acceptor);
  void start(const std::string& peer_host, const std::string& peer_port);
  void stop();
  // void add_connection(connection& connection_);
  // void remove_connection(connection& connection_);

  const io_context& get_io_context() const { return this->io_context_; }

 private:
  awaitable<void> start_connection(tcp::socket client);

  io_context io_context_;
  std::unique_ptr<tcp::acceptor> acceptor_;

  // // protects add/remove connections
  // boost::mutex connections_mutex_;

  // // protected by connections_mutex_
  // std::set<connection&> connections_;

  // thread group to run io_context
  boost::thread_group threads_;
};

}  // namespace p2p
}  // namespace bp

#endif
