package soc_timer_reg_pkg;
    // Defining what registers are where in memory (memory mapping), what CTRL register 
    // -------------------------------
    // Register Offsets (AXI address offsets)
    // -------------------------------
    localparam logic [31:0] LOAD_REG_OFFSET        = 32'h00;  // Write-only // Load Register Value
    localparam logic [31:0] CONTROL_REG_OFFSET     = 32'h04;  // Read/Write // Control Register: MASK, RELOAD, EN
    localparam logic [31:0] COUNTER_REG_OFFSET     = 32'h08;  // Read-only  // Get Counter value
    localparam logic [31:0] INT_STATUS_REG_OFFSET  = 32'h0C;  // Read-only  // If timer has triggered interrupt or not
    localparam logic [31:0] INT_CLEAR_REG_OFFSET   = 32'h10;  // Write-only // Clear Interrupt

    // -------------------------------
    // CONTROL_REG Bitfield Definitions
    // -------------------------------
    localparam int CTRL_ENABLE_BIT        = 0; // Bit 0: Enable countdown
    localparam int CTRL_AUTO_RELOAD_BIT   = 1; // Bit 1: Auto-reload when counter reaches 0
    localparam int CTRL_IRQ_MASK_BIT      = 2; // Bit 2: Mask irq_out signal (1 = disable)

    // -------------------------------
    // INT_STATUS_REG Bitfield Definitions
    // -------------------------------
    localparam int IRQ_FLAG_BIT           = 0; // Bit 0: Set when timer reaches 0

    // -------------------------------
    // INT_CLEAR_REG Action
    // -------------------------------
    // Bit 0: Write 1 to clear irq_flag. No readback.

endpackage
