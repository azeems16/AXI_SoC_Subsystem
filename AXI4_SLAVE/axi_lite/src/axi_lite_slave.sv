module axi_lite_slave #(
    parameter int          NUM_REGS   = 4     ,
    parameter integer      ADDR_WIDTH = 32    ,
    parameter integer      DATA_WIDTH = 32    ,
    parameter logic [31:0] BASE_ADDR  = 32'h0
)(
// ---------------------------
// AXI-Lite Slave Interface
// ---------------------------
    input logic ACLK,
    input logic ARESETN,

    // Write Address Channel
    input  logic [ADDR_WIDTH-1:0]       S_AXI_AWADDR  , // Address to write to
    input  logic                        S_AXI_AWVALID , // Handshake signal from master to indicate ready/valid
    output logic                        S_AXI_AWREADY , // Handshake signal from slave to indicate ready/valid

    // Write Data Channel
    input  logic [DATA_WIDTH-1:0]       S_AXI_WDATA  , // data that will be written
    input  logic [(DATA_WIDTH/8)-1:0]   S_AXI_WSTRB  , // 
    input  logic                        S_AXI_WVALID , // Handshake signal from master to indicate ready/valid
    output logic                        S_AXI_WREADY , // Handshake signal from slave to indicate ready/valid

    // Write Response Channel
    output logic [1:0]                  S_AXI_BRESP  , // signal for slave to indicate status of write ; 2'b00: OKAY, 2'b01: unused, 2'b10: SLVERR, 2'b11: DECERR
    output logic                        S_AXI_BVALID , // handshake signal from slave to indicate response is ready/valid
    input  logic                        S_AXI_BREADY , // handshake signal from master to indicate ready to receive response

    // Read Address Channel
    input  logic [ADDR_WIDTH-1:0]       S_AXI_ARADDR  , // Address to read from
    input  logic                        S_AXI_ARVALID , // Handshake signal from master to indicate ready/valid
    output logic                        S_AXI_ARREADY , // Handshake signal from slave to indicate ready/valid

    // Read Data Channel
    output logic [DATA_WIDTH-1:0]       S_AXI_RDATA  , // data that will be written
    output logic [1:0]                  S_AXI_RRESP  , // signal for slave to indicate status of read
    output logic                        S_AXI_RVALID , // Handshake signal from slave  to indicate ready/valid
    input  logic                        S_AXI_RREADY   // Handshake signal from master to indicate ready/valid

);
logic [DATA_WIDTH-1:0] regfile [NUM_REGS-1:0];  // (NUM_REGS-1 registers each 32-bit): 0x00, 0x04, 0x08, 0x0C
localparam int ADDR_INDEX_WIDTH = $clog2(NUM_REGS);

task automatic reset_regfile();
    for (int i = 0; i < NUM_REGS; i++) begin
        regfile[i] = 32'd0;
    end
endtask

// Register index signals 
logic [ADDR_INDEX_WIDTH-1:0] wr_addr_idx;
logic [ADDR_INDEX_WIDTH-1:0] rd_addr_idx;

logic [ADDR_WIDTH-1:0] addr_offset;
assign addr_offset = S_AXI_AWADDR - BASE_ADDR;
// Enables, handshake and intermediary variables
logic write_en, read_en;
logic awc_hs, wc_hs, ar_hs, r_hs; // handshake tracker flags
logic [DATA_WIDTH-1:0] rdata, wdata;
logic [1:0]  aw_err, ar_err;
assign write_en = awc_hs & wc_hs;
assign read_en  = ar_hs & S_AXI_RREADY;

// Design Note:
// AXI-Lite enforces 32-bit (4-byte) alignment,
// so address bits [1:0] are always 0 and can be ignored.
// We use bits [3:2] to select between 4 registers mapped at:
// 0x00, 0x04, 0x08, and 0x0C.

always_ff @(posedge ACLK) begin
    if (!ARESETN) begin
        reset_regfile();
        S_AXI_AWREADY <=  0;
        S_AXI_WREADY  <=  0;
        S_AXI_BVALID  <=  0;
        S_AXI_BRESP   <= '0;
        awc_hs        <=  0;
        wc_hs         <=  0;
        ar_hs         <=  0;

        S_AXI_ARREADY <=  0;
        S_AXI_RVALID  <=  0;
        S_AXI_RDATA   <=  0;
        S_AXI_RRESP   <= '0;
        aw_err        <= '0;
        ar_err        <= '0;
    end
// ---------------------------
// Write Path
// ---------------------------
    // Address Handshake: check handshake and ensure we have no pending transaction (BVALID || awc_hs)
    if (S_AXI_AWVALID && !S_AXI_BVALID && !awc_hs) begin  
        S_AXI_AWREADY <= 1;                               
        awc_hs        <= 1;                               
        wr_addr_idx   <= S_AXI_AWADDR[ADDR_INDEX_WIDTH + 1 : 2]; // 4-byte aligned: 00, 01, 10, 11
        
        // Error Checking
        if((addr_offset >> 2) >= NUM_REGS) begin
            aw_err <= 2'b10;                          
            $display("Slave Error: Address is out permissible range"); // SLVERR
        end     

        if(S_AXI_WSTRB == '0) begin
            aw_err <= 2'b10;                          // SLVERR
            $display("Slave Error: S_AXI_WSTRB shows no valid bytes to write to");
        end     
    end

    // Write Handshake: check handshake and ensure we have no pending transaction (BVALID || wc_hs)
    if (S_AXI_WVALID && !S_AXI_BVALID && !wc_hs) begin  
        S_AXI_WREADY <= 1;                       
        wc_hs        <= 1;                       
        wdata        <= S_AXI_WDATA;
    end                                  

    // Pulldowns: in successive clock edge, if handshake flag is already preset, clear *READY signal
    if (awc_hs) begin                
        S_AXI_AWREADY <= 0;         
    end

    if (wc_hs) begin                
        S_AXI_WREADY <= 0;        
    end

    // Set both handshakes down to mark end of transaction
    if (S_AXI_BREADY && S_AXI_BVALID) begin          
        S_AXI_BVALID <= 0;        
        awc_hs       <= 0;
        wc_hs        <= 0;

    end

    // Write
    if (write_en) begin
        if(aw_err == 2'b11) begin

        end
        else if(aw_err == 2'b10) begin  // Reset all handshake flags, send response to master
            awc_hs               <= 0;           
            wc_hs                <= 0;           
            S_AXI_BVALID         <= 1;           
            S_AXI_BRESP          <= 2'b10;        
        end
        else begin

        // Design Note: WSTRB is used to write to specific bytes in a register, can be for register sharing, byte designations, partial word writes 
        for (int i = 0; i < DATA_WIDTH/8; i++) begin
            if (S_AXI_WSTRB[i]) begin
            regfile[wr_addr_idx][8*i +: 8] <= wdata[8*i +: 8];
            end
        end

        awc_hs               <= 0;          
        wc_hs                <= 0;          
        S_AXI_BVALID         <= 1;          
        S_AXI_BRESP          <= 2'b00;      
        end
    end

// ---------------------------
// Read Path
// ---------------------------
    // Address Handshake
    if (S_AXI_ARVALID && !ar_hs) begin 
        S_AXI_ARREADY <= 1;          
        ar_hs         <= 1;
        rd_addr_idx   <= S_AXI_ARADDR[ADDR_INDEX_WIDTH + 1 : 2];
    end

    // Read Handshake
    if (ar_hs && S_AXI_RREADY) begin         
        rdata        <= regfile[rd_addr_idx];
        S_AXI_RVALID <= 1;                   
        S_AXI_RDATA  <= rdata;               
        S_AXI_RRESP  <= 2'b00; // OKAY       
        ar_hs        <= 0;                   
    end

    if (ar_hs) begin
        S_AXI_ARREADY <= 0;
    end

    if (S_AXI_RREADY && S_AXI_RVALID) begin
        S_AXI_RVALID <= 0;
    end
end

// ---------------------------
// Assertions: AXI-Lite Protocol Handshakes & Validity Checks
// ---------------------------

assert property (@(posedge ACLK) disable iff (!ARESETN)
    S_AXI_AWREADY |-> S_AXI_AWVALID
) else $error("AXI Protocol Violation: AWREADY was asserted without AWVALID (write address channel)");

assert property (@(posedge ACLK) disable iff (!ARESETN)
    S_AXI_WREADY |-> S_AXI_WVALID
) else $error("AXI Protocol Violation: WREADY was asserted without WVALID (write data channel)");

assert property (@(posedge ACLK) disable iff (!ARESETN)
    S_AXI_ARREADY |-> S_AXI_ARVALID
) else $error("AXI Protocol Violation: ARREADY was asserted without ARVALID (read address channel)");

assert property (@(posedge ACLK) disable iff (!ARESETN)
    S_AXI_WVALID |-> (S_AXI_WSTRB != 4'b0000)
) else $error("AXI Protocol Violation: WVALID asserted with no active byte lanes (WSTRB == 0)");

assert property (@(posedge ACLK) disable iff (!ARESETN)
    S_AXI_BVALID |-> (write_en || aw_err == 2'b10)
) else $error("AXI Protocol Violation: BVALID asserted without a valid write or address error condition");

assert property (@(posedge ACLK) disable iff (!ARESETN)
    S_AXI_RVALID |-> ##[0:$] S_AXI_RREADY
) else $error("AXI Protocol Violation: RVALID asserted but RREADY was never observed (read data handshake never completed)");

endmodule