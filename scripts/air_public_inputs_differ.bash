#!/usr/bin/env bash

delta \
    <(jq -S . "$1") \
    <(jq -S . "$2") \
    -s
