ARG TARGETPLATFORM=linux/amd64
FROM --platform=${TARGETPLATFORM} ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive \
    PATH="/workspace/AutoQ/build/cli:${PATH}"

SHELL ["/bin/bash", "-c"]

# Install build dependencies
RUN apt-get update && apt-get install -y \
    git \
    g++ \
    make \
    cmake \
    libboost-filesystem-dev \
    libboost-test-dev \
    libboost-regex-dev \
    python3 \
    texlive-latex-extra \
    texlive-latex-base \
    texlive-latex-recommended \
    libvips-tools

# Create workspace directory and copy source code
WORKDIR /workspace
COPY . AutoQ

# Build the project (visible in docker build output)
WORKDIR /workspace/AutoQ
RUN make 2>&1 | tee build.log

# Run unit tests to verify build
RUN make test 2>&1 | tee test.log

# Create a helper script to run example benchmarks
RUN echo '#!/bin/bash' > /usr/local/bin/run_benchmarks.sh && \
    echo 'echo "=== Running example benchmarks ==="' >> /usr/local/bin/run_benchmarks.sh && \
    echo 'cd /workspace/AutoQ' >> /usr/local/bin/run_benchmarks.sh && \
    echo '/workspace/AutoQ/run.sh 2>&1' >> /usr/local/bin/run_benchmarks.sh && \
    echo 'echo "=== Benchmarks completed ==="' >> /usr/local/bin/run_benchmarks.sh && \
    chmod +x /usr/local/bin/run_benchmarks.sh

# Set default command to bash with a welcome message
CMD ["/bin/bash", "-c", "echo \"AutoQ container ready. Use 'run_benchmarks.sh' to run example benchmarks.\"; bash"]
