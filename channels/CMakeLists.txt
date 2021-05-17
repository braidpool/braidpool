cmake_minimum_required(VERSION 3.10)

# set the project name
project(one_way_channel VERSION 1.0)

find_package(PkgConfig REQUIRED)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED True)

configure_file(one_way_channel_config.h.in one_way_channel_config.h)

pkg_check_modules(LIBBITCOIN-SYSTEM libbitcoin-system)

add_subdirectory(channel)

# message(STATUS ${LIBBITCOIN-SYSTEM_LINK_LIBRARIES})
list(APPEND EXTRA_LIBS channel)
list(APPEND EXTRA_INCLUDES "${PROJECT_SOURCE_DIR}/channel/include")

list(APPEND EXTRA_LIBS ${LIBBITCOIN-SYSTEM_LINK_LIBRARIES})
list(APPEND EXTRA_INCLUDES ${LIBBITCOIN-SYSTEM_INCLUDE_DIRS})
# message(STATUS ${EXTRA_LIBS})


# add the executable
add_executable(one_way_channel one_way_channel.cpp)

target_link_libraries(one_way_channel PUBLIC ${EXTRA_LIBS})

target_include_directories(one_way_channel PUBLIC
  "${PROJECT_BINARY_DIR}"
  ${EXTRA_INCLUDES}
  )

install(TARGETS one_way_channel DESTINATION bin)
install(FILES "${PROJECT_BINARY_DIR}/one_way_channel.h"
  DESTINATION include
  )
