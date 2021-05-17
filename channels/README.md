# One Way Channels

Braidpool uses one way channels for distributing payouts to
participating miners.

This directory has a simple CLI tool to geneate transactions for

- Fund transactions
- Refund transactions
- Channel update transactions

The `channel` directory has a library that will be used for braidpool

The root directory has a CLI tool for generating transactions by
providing keys as relevant.

# Usage

`./one_way_channel --create-fund-tx --funder <> --receiver <>`

`./one_way_channel --create-refund-tx --funder <> --receiver <>`

`./one_way_channel --create-channel-update-tx --funder <> --receiver <>`

`./one_way_channel --create--tx --funder <> --receiver <>`

