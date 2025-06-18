# Braidpool Documentation

* [Overview](overview.md) is a high-level overview of the braidpool project
* [General Considerations](general_considerations.md) discusses some of the design decisions for any
  decentarlized mining pool
* [Braidpool Specification](braidpool_spec.md) is the main specification for braidpool
* [Bitcoin Hashrate Derivatives Trading](derivatives.md) describes how we can replace FPPS with a
  marketplace of hashrate forwards or options
* [Roadmap](roadmap.md) is the roadmap for braidpool

# Works in Progress
* [Braidpool Consensus](braid_consensus.md) is a draft specification for the consensus rules
  of braidpool.

# Tests

* We have an extensive test suite for the Braid consensus algorithm written in Python. To run these
  tests:

```sh
cd tests
python -m venv venv
source venv/bin/activate
pip install -r requirements.txt
python braid.py
```

* We also have a test suite for the Braidpool protocol written in Rust. To run these tests:

```sh
cargo test
```

* We have a network simulator written in python that simulates a global network of miners
  distributed on the surface of the earth and using realistic latencies. To run this simulation:

```sh
cd tests
python simulator.py
```

* Finally you can use both these python test suites in an iPython notebook with some nice graphing
  of braids and cohorts:

```sh
cd tests
jupyter notebook "Braid Example.ipynb"
```
# License

Braidpool is licensed under the AGPL license.
