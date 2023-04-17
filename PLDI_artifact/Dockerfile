FROM ubuntu:latest

ENV TZ=Asia/Taipei \
    DEBIAN_FRONTEND=noninteractive

COPY . /home

RUN apt-get update && apt-get install -y \
    time \
    make \
    cmake \
    g++ \
    libboost-filesystem-dev \
    libboost-test-dev \
    vim \
    texlive-latex-extra \
    python3-pip \
    libffi7 \
    && pip3 install mqt.qcec==2.0.0

WORKDIR /home
CMD ["/bin/bash"]
