package dma_regfile;
// Defining what registers are where in memory (memory mapping), what CTRL register 

// -------------------------------
// Register Offsets (AXI-Lite mapped)
// -------------------------------
localparam logic [31:0] SRC_ADDR  = 32'h00;  // R/W — Source address of DMA transfer
localparam logic [31:0] DST_ADDR  = 32'h04;  // R/W — Destination address
localparam logic [31:0] LENGTH    = 32'h08;  // R/W — Number of bytes to transfer
localparam logic [31:0] CONTROL   = 32'h0C;  // W   — Bit[0] = Start; Bit[1] = IRQ Enable
localparam logic [31:0] STATUS    = 32'h10;  // R   — Bit[0] = Done; Bit[1] = Error
localparam logic [1:0 ] BURST     = 32'h14;  // R/W — Bit[1:0]: 00 = FIXED, 01 = INCR, 10 = WRAP, 11 = ERR

// -------------------------------
// CONTROL Bitfield Definitions
// -------------------------------
localparam int CTRL_START_BIT      = 0; // Bit 0: START transfer
localparam int CTRL_IRQ_EN_BIT     = 1; // Bit 1: Enable interrupt on completion

// -------------------------------
// STATUS Bitfield Definitions
// -------------------------------
localparam int STATUS_DONE_BIT     = 0; // Bit 0: Transfer complete
localparam int STATUS_ERR_BIT      = 1; // Bit 1: Error occurred (e.g., misaligned addr)

endpackage