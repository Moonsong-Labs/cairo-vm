#!/usr/bin/env bash
#
# outputs memory file in "ADDR VALUE" format, on cell per line

hexdump -e '1/8 "%10u " 4/8 "%x " "\n"' "$1" | sort -n
