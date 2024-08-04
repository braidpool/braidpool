FROM rust:1.80.0
LABEL description="Rust dev sandbox"

RUN apt-get -y update

WORKDIR "/usr/src/braidpool/node"

COPY ./node .

CMD ["/bin/bash"]
