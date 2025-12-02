FROM ubuntu:latest

ENV TZ=Asia/Taipei \
    DEBIAN_FRONTEND=noninteractive \
    PATH="/root/AutoQ/build/cli:${PATH}"

SHELL ["/bin/bash", "-c"]
# texlive-latex-extra texlive-latex-base texlive-latex-recommended libvips-tools
RUN apt update && apt install -y python3 git git-lfs g++ make cmake libboost-filesystem-dev libboost-test-dev libboost-regex-dev libantlr4-runtime-dev
RUN mkdir -p /root/AutoQ
COPY . /root/AutoQ

WORKDIR /root
CMD ["/bin/bash"]
