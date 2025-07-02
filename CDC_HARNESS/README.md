# CDC Harness (Async FIFO)

A self-contained asynchronous FIFO with CDC (Clock Domain Crossing) handling. This project includes full SystemVerilog RTL, assertions (SVA), testbench with randomized transactions, and functional coverage tracking via covergroups.

---

## Directory Structure

```
cdc_harness/
├── rtl/            # RTL modules (fifo, synchronizers)
├── tb/             # Testbench and testbench-related files
├── coverage/       # Covergroup and SVA assertions
├── run.do          # Simulation script for Riviera-PRO
├── dump.vcd        # Waveform output (generated after run)
├── cov.txt         # Coverage report (generated after run)
└── README.md
```

---

## How to Run

```sh
vlib work
vlog -timescale 1ns/1ns rtl/*.sv tb/*.sv coverage/*.sv
vsim -c -do run.do
```

Make sure your `run.do` file contains:

```tcl
vsim +access+r;
run -all;
acdb save;
acdb report -db fcover.acdb -txt -o cov.txt -verbose
exec cat cov.txt;
exit
```

This script compiles, runs simulation, saves coverage to `fcover.acdb`, generates a detailed report as `cov.txt`, and prints it to console.

---

## Features

- Clean FIFO design using Gray-coded pointers and synchronizers
- Reset handling for both clock domains
- SystemVerilog Assertions (SVA) for:
  - Write during full
  - Read during empty
- Functional coverage:
  - `wr_en` × `wr_full` cross
  - `rd_en` × `rd_empty` cross
- Full waveform dump and coverage report
- Parameterized data width

---

## Simulation Output

After simulation, you'll get:

- `dump.vcd`: for waveform viewing
- `cov.txt`: readable report from `fcover.acdb`

You can explore FSM transitions, timing behavior, and assertion triggers visually.

---

## Author

Azeem Shah  
[github.com/azeems16](https://github.com/azeems16)

### Simulation Notes

This project was fully simulated on **EDA Playground** for cross-compatibility and ease of use.

- Functional simulation was verified using:
  - **Cadence Xcelium 23.09**
- Coverage was collected using:
  - **Aldec Riviera-PRO 2023.04**  
    (Other simulators may not support functional coverage in the same way.)

> If you want to view coverage (`acdb`, `.ucdb`, or `*.vdb`) or generate coverage reports, **use Aldec Riviera-PRO 2023.04** or later.