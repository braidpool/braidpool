list( APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/modules" )

pkg_check_modules(LIBBITCOIN-SYSTEM libbitcoin-system)

find_package( Secp256K1 0.1.0.19 REQUIRED )

include_directories(${PROJECT_SOURCE_DIR}/channel/include/ ${LIBBITCOIN-SYSTEM_INCLUDE_DIRS})

add_library(channel
  src/channel_transaction.cpp
  src/funding_transaction.cpp
  src/refund_transaction.cpp
  src/channel_update_transaction.cpp
  )

## Testing

enable_testing()

find_package(Boost COMPONENTS system filesystem unit_test_framework REQUIRED)

add_executable(channel_test
  ${PROJECT_SOURCE_DIR}/channel/tests/main.cpp
  ${PROJECT_SOURCE_DIR}/channel/tests/funding_transaction_test.cpp
  )

target_link_directories(channel_test PUBLIC
  ${secp256k1_LIBDIR}
  )

target_link_libraries(channel_test
  channel
  ${LIBBITCOIN-SYSTEM_LINK_LIBRARIES}
  ${Boost_FILESYSTEM_LIBRARY}
  ${Boost_SYSTEM_LIBRARY}
  ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY}
  ${secp256k1_LIBRARIES}
  "-lpthread"
  "gmp"
  )

add_test(NAME channel_library_test
  COMMAND ./channel_test)
