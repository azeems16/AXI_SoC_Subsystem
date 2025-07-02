# AXI4 Slave (Parameterized RTL + Testbench)

## Overview
This project implements a parameterized AXI4 slave module with support for burst transfers, byte-wise write masking, and basic error handling. A matching testbench drives full AXI traffic, including valid/ready handshakes across all channels.

## Features

- Full AXI4 support (write/read address, data, response channels)
- Supports burst types: FIXED, INCR, WRAP
- Byte-level WSTRB write masking
- Parameterized interface:
  - DATA_WIDTH
  - ADDR_WIDTH
  - ID_WIDTH
  - NUM_REGS
- Burst alignment and register decoding based on ADDR_LSB and ADDR_INDEX_W
- Handles error conditions:
  - Out-of-range addresses
  - Invalid burst types
  - WSTRB = 4'b0000

## Parameters

| Name         | Description                        | Default |
|--------------|------------------------------------|---------|
| DATA_WIDTH   | AXI data bus width (must be power of 2) | 32      |
| ADDR_WIDTH   | AXI address width                  | 32      |
| ID_WIDTH     | Width of AXI transaction IDs       | 4       |
| NUM_REGS     | Number of internal registers       | 4       |

Derived locals include:
- ADDR_LSB = $clog2(DATA_WIDTH / 8)
- ADDR_INDEX_W = $clog2(NUM_REGS)

## Testbench Highlights

- Parameterized to match DUT
- Includes five major test segments:
  1. Single-beat transactions
  2. Multi-beat FIXED burst
  3. Multi-beat INCR burst
  4. Multi-beat WRAP burst
  5. Error testing: invalid address, burst type, WSTRB
- Uses forked handshakes and waveform dumps via $dumpvars
- Tasks `read()` and `write()` simulate AXI behavior across all phases

## Waveform Debugging

- VCD output saved via `$dumpfile("dump.vcd")`
- Dumps register file contents and FSM state (`wr_state`) for post-simulation analysis

## Possible Extensions

- Functional coverage hooks (burst types, wstrb masks, handshakes)
- Formal assertions for AXI4 compliance
- UVM-lite test wrapper or scoreboard
- Optional read/write latency insertion