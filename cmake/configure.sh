#!/bin/bash

# sudo needed
if [ "$EUID" -ne 0 ]; then
  echo "Please use sudo [path]/configure.sh to run the script"
  exit 1
fi

OS_TYPE=$(uname -s)

echo "Operating System: $OS_NAME"

if [ "$OS_TYPE" = "Linux" ]; then

  # Linux type
  if [ -f /etc/os-release ]; then
    . /etc/os-release
    OS_NAME=$ID
    OS_VERSION=$VERSION_ID


    case $OS_NAME in
      ubuntu|debian)
        apt install g++
        apt install make
        apt install cmake
        apt install libboost-filesystem-dev
        apt install libboost-test-dev
        ;;
      *)
        echo "UNSUPPORTED LINUX VERSION: $OS_NAME"
        exit 1
        ;;
    esac
  else
    echo "/etc/os-release not found."
    exit 1
  fi

elif [ "$OS_TYPE" = "Darwin" ]; then
    if ! command -v brew &> /dev/null; then
        echo "Homebrew not found. Please make sure you have brew installed"
        #/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
    fi
    brew install gcc
    brew install make
    brew install cmake
    brew install boost
else
  echo "UNSUPPORTED OS: $OS_TYPE"
  #exit 1
fi

SCRIPT_DIR=$(cd "$(dirname "$0")"; pwd -P)

cd "$SCRIPT_DIR/.."
mkdir ./build

