# AXI SoC Subsystem Projects

This repository contains a set of self-contained RTL design modules and subsystems, each focused on a specific digital design concept using Verilog/SystemVerilog.

Each project includes clean, testable code and is structured for easy simulation and integration.

---

## 📁 Projects Overview

### 🔹 [AXI4_SLAVE](./AXI4_SLAVE)
- Implements a full AXI4-compliant slave interface.
- Supports burst transfers (INCR, WRAP), WSTRB masking, transaction IDs, and error signaling.
- Designed for SoC integration and testing.

### 🔹 [CDC_HARNESS](./CDC_HARNESS)
- A clock-domain crossing harness featuring asynchronous FIFOs and reset synchronizers.
- Includes SVA assertions and functional coverage points.
- Good for verifying safe data handoff across clock boundaries.

### 🔹 [DMA_CONTROLLER](./DMA_CONTROLLER)
- AXI Master DMA engine supporting descriptor-based transfers.
- Handles burst reads/writes and stream output.
- Includes a finite-state control mechanism and optional AXIS output.

### 🔹 [SOC_TIMER_IP](./SOC_TIMER_IP)
- A configurable timer peripheral built for SoC systems.
- Register-mapped AXI-Lite interface and interrupt generation.
- Simulation-ready with testbench and parameterization.

### 🔹 [SPI_I2C_BRIDGE](./SPI_I2C_BRIDGE)
- Connects an SPI master to an I2C slave using a FIFO bridge.
- Demonstrates cross-protocol interfacing and simple glue logic.
- Verifies serial transmission using FSMs and bus arbitration.

---

## 🛠️ Usage

Each project is meant to be standalone. To simulate or integrate:

1. Navigate to the project folder.
2. Review included testbenches or simulation instructions.
3. Run your simulator (e.g., Icarus Verilog, ModelSim, Vivado) as needed.

You can clone the entire repo or use individual folders as IP blocks in your SoC-level design.

---

## 📌 Notes

- All projects are built and tested in isolation.
- `.gitignore` excludes simulation outputs and tool-generated files.
- Future additions may include formal verification, UVM testbenches, or AXI interconnect integration.

---

## 👤 Author

Azeem Shah  
RTL / SoC Design Enthusiast  
📍 Canada  
