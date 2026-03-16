FROM ubuntu:22.04

# Avoid prompts during installation
ENV TZ=Asia/Taipei \
    DEBIAN_FRONTEND=noninteractive \
    PATH="/root/AutoQ/build/cli:${PATH}"

SHELL ["/bin/bash", "-c"]
RUN apt update && apt install -y python3 git git-lfs g++ make cmake libboost-filesystem-dev libboost-test-dev libboost-regex-dev libantlr4-runtime-dev
WORKDIR /workspaces/AutoQ
CMD ["/bin/bash"]
