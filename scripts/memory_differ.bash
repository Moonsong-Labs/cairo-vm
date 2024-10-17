#!/usr/bin/env bash

delta \
    <(hexdump -e '1/8 "%u " 4/8 "%x " "\n"' "$1" | sort -n) \
    <(hexdump -e '1/8 "%u " 4/8 "%x " "\n"' "$2" | sort -n) \
    -s
