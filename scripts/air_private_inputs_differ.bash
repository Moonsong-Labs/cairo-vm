#!/usr/bin/env bash

delta \
    <(jq -S 'del(.memory_path,.trace_path)' "$1") \
    <(jq -S 'del(.memory_path,.trace_path)' "$2") \
    -s
