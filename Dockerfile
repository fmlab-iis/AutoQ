FROM ubuntu:latest

ENV TZ=Asia/Taipei \
    DEBIAN_FRONTEND=noninteractive \
    PATH="/root/AutoQ/build/cli:${PATH}"

SHELL ["/bin/bash", "-c"]
RUN apt-get update && apt-get install -y g++ make cmake libboost-filesystem-dev libboost-test-dev libboost-regex-dev python3 texlive-latex-extra texlive-latex-base texlive-latex-recommended libvips-tools
RUN mkdir -p /root/AutoQ
COPY . /root/AutoQ

WORKDIR /root
CMD ["/bin/bash"]
