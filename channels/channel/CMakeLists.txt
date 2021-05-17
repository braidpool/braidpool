pkg_check_modules(LIBBITCOIN-SYSTEM libbitcoin-system)

include_directories(${PROJECT_SOURCE_DIR}/channel/include/ ${LIBBITCOIN-SYSTEM_INCLUDE_DIRS})

add_library(channel src/channel.cpp)
