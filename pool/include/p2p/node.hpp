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
#include <memory>
#include <p2p/connection.hpp>
#include <p2p/define.hpp>
#include <set>

#include "runner.hpp"

namespace bp {
namespace p2p {
class node : private boost::noncopyable {
 public:
  node(io_context& ctx, const std::string& listen_address,
       const std::string& listen_port);
  ~node();
  void start();
  void stop();
  awaitable<void> connect_to_peers(const std::string& host,
                                   const std::string& port);

 private:
  awaitable<void> listen(tcp::acceptor& acceptor);

  void add_connection(connection::connection_ptr connection_);
  void remove_connection(connection::connection_ptr connection_);

  std::unique_ptr<tcp::acceptor> acceptor_;

  io_context& ctx_;

  // protects add/remove connections
  boost::mutex connections_mutex_;

  // protected by connections_mutex_
  std::set<connection::connection_ptr> connections_;
};

}  // namespace p2p
}  // namespace bp

#endif
