#!/usr/bin/env bash

git submodule init

mkdir -p ~/.agda
touch ~/.agda/libraries
echo "$(pwd)/agdarsec/.agda-lib" >> ~/.agda/libraries
