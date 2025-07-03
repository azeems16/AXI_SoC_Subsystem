
# SPI to I2C FIFO Bridge (Multi-Clock Domain RTL Design)

## Overview
This project implements a **complete RTL subsystem** that bridges two distinct serial protocols operating on different clock domains:
- **SPI Slave** (write-side)
- **Asynchronous FIFO** (CDC handling)
- **I2C Slave** (read-side)

Data is written into the FIFO from the SPI slave and read out by an I2C master using read-only addressed access. The system handles all synchronization, buffering, and protocol-specific behavior with realistic timing and safety considerations.

---

## Top-Level Modules

### 1. `spi_slave`
**Function:** Receives 8-bit frames over SPI and pushes them into a write-domain FIFO.

- Parameterized for frame width (default 8 bits)
- Detects rising edges on `sclk` using a 2-stage synchronizer
- Active-low `cs_n` gating and reset of bit counters
- Automatically asserts `wr_en` after a full byte is received
- Ignores incoming bits when FIFO is full

**Key Protections:**
- Byte capture only happens on valid rising edges of `sclk`
- Drops extra bits when FIFO full (warning message generated)

### 2. `cdc_async_fifo`
**Function:** Buffers data between two independent clock domains.

- Parameterized for data width and FIFO depth
- Uses Gray-coded write/read pointers
- Synchronizes pointers across domains via `cdc_2flop_sync`
- Output available when write and read pointers don't match

### 3. `i2c_slave`
**Function:** Responds to I2C read requests by releasing bytes from the FIFO.

- Supports basic read-only I2C address decoding
- Tri-state SDA line with open-drain behavior
- FSM detects START, ADDR, ACK, DATA, STOP
- Waits 2 cycles to safely load from FIFO
- Shifts out data MSB-first, then checks NACK

---

## Testbenches

### `spi_slave_tb`
- Simulates rising edges on `sclk`
- Sends random bytes to the SPI slave
- Handles toggling of `cs_n` to emulate transaction windows

### `i2c_slave_tb`
- Bit-bangs I2C over `sda`/`scl` lines
- Emulates START, address + R bit, ACK, DATA clocking, STOP
- Tests multiple reads from the FIFO
- Monitors SDA line for correct byte delivery and ACK/NACK

---

## SystemVerilog Assertions (SVA)
### `spi_sva.sv`
- `off_if_not_selected`: wr_en must not assert unless `cs_n` is low
- `off_when_full`: wr_en must not assert if FIFO is full
- `valid_write_conditions`: wr_en can only assert if FIFO isn't full and `cs_n` is low

### `i2c_sva.sv`
- `no_read_when_empty`: rd_en must not assert when FIFO is empty
- `no_toggle_unless_reading`: `scl`/`sda` signals must stay stable unless actively reading

Each module includes its corresponding `*_sva.sv` monitor connected at the testbench level.

---

## Integration Module
### `spi_fifo_i2c_top`
This top-level module instantiates:
- `spi_slave`
- `cdc_async_fifo`
- `i2c_slave`

It wires together the system for real-time SPI-to-I2C bridging. FIFO handles CDC, and both serial interfaces are treated with proper domain isolation.

---

## Features Checklist
- [x] **Full RTL design with proper modularization**
- [x] **Multi-clock domain support** via async FIFO
- [x] **Open-drain SDA logic** with pull-up behavior
- [x] **2FF synchronizers** for metastability protection
- [x] **SystemVerilog Assertions (SVA)** for protocol safety
- [x] **Realistic testbenches** with edge-level I2C + SPI emulation
- [x] **Parameterizable data widths and addresses**
- [x] **Tri-state and ACK/NACK handling** for I2C

---

## Future Improvements
- Add backpressure handling or byte-drop signaling
- Enhance testbench coverage with full UVM-lite integration
- Support I2C write transactions (currently read-only)

---

## How to Run
1. Run with any open-source simulator (e.g., `Icarus Verilog`, `Verilator`)
2. Check `dump.vcd` in waveform viewer to analyze signal transitions
3. Modify `rd_data` and `rd_empty` in TB to simulate various FIFO states

```sh
# Example (Icarus Verilog)
iverilog -g2012 spi_slave_tb.sv -o spi_tb && vvp spi_tb
```

---

## Author Notes
This project was developed as part of a broader RTL design arc focused on multi-protocol, clock-domain crossing, and assertion-based verification. It reflects a real-world, job-ready skillset in:
- Digital design
- Testbench development
- Assertion writing
- Protocol decoding and timing
- CDC-safe architecture

Feel free to fork and extend!
