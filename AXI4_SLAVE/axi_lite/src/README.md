# AXI-Lite Slave (SystemVerilog)

This project implements a synthesizable AXI-Lite slave interface in SystemVerilog. It supports full read/write handshakes, address decoding, SLVERR handling, and WSTRB byte masking for a memory-mapped register block.

## Features

- Full AXI-Lite compliance (AW, W, B, AR, R)
- 32-bit wide registers with byte-lane WSTRB masking
- `NUM_REGS` and `BASE_ADDR` parameterized
- SLVERR support for out-of-range accesses and invalid WSTRB
- Clean testbench with multiple transactions and GTKWave support
- Simulation-only assertions for handshake validity

## Parameters

```systemverilog
parameter int NUM_REGS = 4;
parameter logic [31:0] BASE_ADDR = 32'h0000_0000;
```

## Register Map

| Offset | Register      |
|--------|---------------|
| 0x00   | regfile[0]    |
| 0x04   | regfile[1]    |
| 0x08   | regfile[2]    |
| 0x0C   | regfile[3]    |

## Simulation

```bash
# Compile and run
iverilog -g2012 -o sim.out axi_lite_slave_tb.sv axi_lite_slave.sv
vvp sim.out
```

## View Waveform

```bash
gtkwave dump.vcd
```

## File List

- `axi_lite_slave.sv` – RTL module
- `axi_lite_slave_tb.sv` – Testbench
- `dump.vcd` – Generated waveform
- `README.md` – This file
