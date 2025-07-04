# SoC Timer Module

## Overview

This project implements a fully functional AXI4-Lite-based timer module for SoC integration. It provides:

- A configurable countdown timer
- Interrupt generation
- Auto-reload and one-shot modes
- AXI4-Lite register-mapped interface for control, load, and status operations

## Features

- **AXI4-Lite Slave Interface** (write/read to timer registers)
- **Interrupt Output** (`irq`)
- **Timer Event Output** (`timer_event`)
- **Internal Register Map**:
  - `LOAD_REG_OFFSET` – load timer value
  - `CONTROL_REG_OFFSET` – enable, auto-reload, mask
  - `INT_CLEAR_REG_OFFSET` – clear interrupt
  - `INT_STATUS_REG_OFFSET` – read interrupt flag
  - `COUNTER_REG_OFFSET` – current timer value (read-only)

## Verification

### Functional Coverage

- 100% functional coverage on:
  - Write access to relevant registers (load, control, interrupt clear)
  - Read access to relevant registers (control, counter, interrupt status)
  - Each control bit (enable, auto-reload, mask) toggled
  - IRQ triggered and cleared
  - All meaningful combinations of control bits covered via `cross`

### SystemVerilog Assertions (SVA)

Assertions are used to ensure protocol correctness and design behavior. Key properties include:

- **IRQ Behavior**
  - If `mask` is set, `irq` must remain low
  - If `counter == 0` and `mask == 0`, `irq` must be asserted
- **Timer Mode Checks**
  - One-shot mode disables timer after single countdown
  - Auto-reload reloads timer on expiry
- **Illegal Register Access**
  - No reads to write-only registers (`INT_CLEAR_REG_OFFSET`)
  - No writes to read-only registers (`INT_STATUS_REG_OFFSET`, `COUNTER_REG_OFFSET`)

### Assertion Status

> Note: Some assertions are currently firing and under investigation. Debug is ongoing to determine if issues lie in testbench stimulus, reset timing, or internal logic corner cases.

## Structure

- `soc_timer.sv`: Timer RTL implementation
- `soc_timer_coverage.sv`: Coverage class capturing all register and functional events
- `testbench.sv`: AXI stimulus and timer exercise
- `soc_timer_reg_pkg.sv`: Register offset constants and bitfield definitions

## Future Improvements

- UVM-based environment for more scalable stimulus
- Randomized tests to complement directed coverage
- Parameterizable timer width and register offsets for SoC configurability
