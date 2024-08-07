#!/bin/bash



OS_TYPE=$(uname -s)

echo "Operating System: $OS_NAME"

if [ "$OS_TYPE" = "Linux" ]; then

  # Linux type
  if [ -f /etc/os-release ]; then
    . /etc/os-release
    OS_NAME=$ID
    OS_VERSION=$VERSION_ID
    # sudo needed
    read -p "using sudo?[y/n]: " yn
    if [[ "$yn" =~ ^[Nn]$ ]]; then
        echo "exit"
        exit 1
    fi
    case $OS_NAME in
      ubuntu|debian)

        
        sudo apt install g++
        sudo apt install make
        sudo apt install cmake
        sudo apt install libboost-filesystem-dev
        sudo apt install libboost-test-dev
        ;;
      *)
        echo "configure.sh only support ubuntu|debian"
        exit 1
        ;;
    esac
  else
    echo "/etc/os-release not found."
    exit 1
  fi

elif [ "$OS_TYPE" = "Darwin" ]; then
    if ! command -v brew &> /dev/null; then
        echo ""
        read -p "Homebrew not found. Do you want to install it?[y/n]: " yn
        if [[ "$yn" =~ ^[Nn]$ ]]; then
            echo "exit"
            exit 1
        else 
          /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
        fi
    fi
    brew install gcc
    brew install make
    brew install cmake
    brew install boost
else
  echo "NOT SUPPORTED OS: $OS_TYPE"
  #exit 1
fi

SCRIPT_DIR=$(cd "$(dirname "$0")"; pwd -P)

cd "$SCRIPT_DIR"
mkdir build

