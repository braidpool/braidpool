FROM rust:1.80.0
LABEL description="Rust dev sandbox"

RUN apt-get -y update

# Copy and build source code
WORKDIR "/usr/src/braidpool/node"
COPY ./node .
RUN cargo build

# By default, open a shell
CMD ["/bin/bash"]
