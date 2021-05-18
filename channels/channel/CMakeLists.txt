pkg_check_modules(LIBBITCOIN-SYSTEM libbitcoin-system)

include_directories(${PROJECT_SOURCE_DIR}/channel/include/ ${LIBBITCOIN-SYSTEM_INCLUDE_DIRS})

add_library(channel src/channel.cpp)

## Testing

enable_testing()

find_package(Boost COMPONENTS system filesystem unit_test_framework REQUIRED)

add_executable(channel_test
  ${PROJECT_SOURCE_DIR}/channel/tests/main.cpp
  ${PROJECT_SOURCE_DIR}/channel/tests/channel_test.cpp
  )

target_link_libraries(channel_test
  ${Boost_FILESYSTEM_LIBRARY}
  ${Boost_SYSTEM_LIBRARY}
  ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY}
  )

add_test(NAME channel_library_test
  COMMAND ./channel_test)
