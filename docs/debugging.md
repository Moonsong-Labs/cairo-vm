# Debugging

## Comparing with Cairo-Lang

If you executed a Cairo0 proof program with both Rust and Python VM, you can use the following scripts to compare their output. They all require `delta` (modern diff) to be installed. If you don't have you can locally change it.

No output when running a differ script implies that there are no differences.

To compare the public inputs, run:
```bash
scripts/air_public_inputs_differ.bash <AIR-PUBLIC-INPUTS-1> <AIR-PUBLIC-INPUTS-2>
```

To compare the private inputs, run:
```bash
scripts/air_private_inputs_differ.bash <AIR-PRIVATE-INPUTS-1> <AIR-PRIVATE-INPUTS-2>
```

If you just want to visualize the memory, run:
```bash
scripts/memory_viewer.bash <MEMORY-FILE>
```
It will output the memory in two columns: address and value


To compare the memory, run:
```bash
scripts/memory_differ.bash <TRACE-1> <TRACE-2>
```
