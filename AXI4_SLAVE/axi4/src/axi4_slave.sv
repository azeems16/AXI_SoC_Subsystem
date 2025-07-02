module axi4_slave #(
    parameter int          NUM_REGS   = 4     ,
    parameter integer      ID_WIDTH   = 4     ,
    parameter integer      ADDR_WIDTH = 32    ,
    parameter integer      DATA_WIDTH = 32    ,
    parameter logic [31:0] BASE_ADDR  = 32'h0
)(
    input  logic                     ACLK,
    input  logic                     ARESETN,

    // Write Address Channel
    input  logic [ID_WIDTH-1:0]       S_AXI_AWID     ,
    input  logic [ADDR_WIDTH-1:0]     S_AXI_AWADDR   ,
    input  logic [7:0]                S_AXI_AWLEN    ,
    input  logic [2:0]                S_AXI_AWSIZE   ,
    input  logic [1:0]                S_AXI_AWBURST  ,
    input  logic                      S_AXI_AWVALID  ,
    output logic                      S_AXI_AWREADY  ,

    // Write Data Channel
    input  logic [DATA_WIDTH-1:0]     S_AXI_WDATA    ,
    input  logic [(DATA_WIDTH/8)-1:0] S_AXI_WSTRB    ,
    input  logic                      S_AXI_WLAST    ,
    input  logic                      S_AXI_WVALID   ,
    output logic                      S_AXI_WREADY   ,

    // Write Response Channel
    output logic [ID_WIDTH-1:0]       S_AXI_BID      ,
    output logic [1:0]                S_AXI_BRESP    ,
    output logic                      S_AXI_BVALID   ,
    input  logic                      S_AXI_BREADY   ,

    // Read Address Channel
    input  logic [ID_WIDTH-1:0  ]     S_AXI_ARID     ,
    input  logic [ADDR_WIDTH-1:0]     S_AXI_ARADDR   ,
    input  logic [7:0]                S_AXI_ARLEN    ,
    input  logic [2:0]                S_AXI_ARSIZE   ,
    input  logic [1:0]                S_AXI_ARBURST  ,
    input  logic                      S_AXI_ARVALID  ,
    output logic                      S_AXI_ARREADY  ,

    // Read Data Channel
    output logic [ID_WIDTH-1:0  ]     S_AXI_RID      ,
    output logic [DATA_WIDTH-1:0]     S_AXI_RDATA    ,
    output logic [1:0]                S_AXI_RRESP    ,
    output logic                      S_AXI_RLAST    ,
    output logic                      S_AXI_RVALID   ,
    input  logic                      S_AXI_RREADY   ,

    // Assertions
    output logic                      write_en        ,
    output logic                      read_en
);
localparam ADDR_LSB     = $clog2(DATA_WIDTH / 8);
localparam ADDR_INDEX_W = $clog2(NUM_REGS);

// TODO: Implement register file and base address decode logic
logic [DATA_WIDTH-1:0] regfile [NUM_REGS-1:0]; // 8 registers, 32 bits/4 bytes wide

// Write-Path FSM
logic [ADDR_INDEX_W-1:0] write_ptr;

typedef enum logic [1:0] {
    WR_IDLE,    // IDLE STATE
    WR_WAIT,    // WAIT FOR HANDSHAKES
    WR_DATA,    // PERFORM WRITE
    WR_RESP     // SEND RESPONSE
} wr_state_t;
wr_state_t wr_state, wr_next;

// Handshake Flags
logic awc_hs, wc_hs; 
//Internal Latches
logic [ADDR_WIDTH-1:0]      addr_latch     ;
logic [ID_WIDTH-1:0]        awid_latch     ;
logic [7:0]  awlen_latch    ;
logic [2:0]  awsize_latch   ;
logic [1:0]  awburst_latch  ;
logic [DATA_WIDTH-1:0]      wdata_latch    ; 
logic [(DATA_WIDTH/8)-1:0]  wstrb_latch    ;
logic                       wlast_latch    ;
logic [ADDR_WIDTH-1:0]      awaddr_latch   ;

// WRAP Burst Latches/Registers
logic [11:0] wr_transfer_size, wr_wrap_start, wr_transfer_size_latch, wr_wrap_start_latch, wr_wrap_end, wr_wrap_end_latch;
assign wr_transfer_size = (awlen_latch + 1)*(2**awsize_latch);
assign wr_wrap_start    = (S_AXI_AWADDR/ wr_transfer_size) * wr_transfer_size;
assign wr_wrap_end      = wr_wrap_start + wr_transfer_size;
// Beat Register
logic [7:0] wr_beat_count; // full AXI burst support

// Error Handling Registers
logic awaddr_err, wstrb_err, wr_burst_err;
// Write Path FSM
always_comb begin
    wr_next = wr_state; // default: retain same state
    case(wr_state)
        WR_IDLE : if (S_AXI_AWVALID || S_AXI_WVALID)                          wr_next = WR_WAIT;
        WR_WAIT : if (awc_hs && wc_hs)                                        wr_next = WR_DATA;
        WR_DATA : if (S_AXI_WLAST || wstrb_err || awaddr_err || wr_burst_err) wr_next = WR_RESP;
        WR_RESP : if (S_AXI_BREADY)                                           wr_next = WR_IDLE;
    endcase
end

always_ff @(posedge ACLK or negedge ARESETN) begin
    if (!ARESETN)
        wr_state <= WR_IDLE;
    else
        wr_state <= wr_next;
end

// Write Path Logic
always_ff @(posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) begin
        S_AXI_AWREADY          <=  0    ;
        awc_hs                 <= '0    ;
        awid_latch             <= '0    ;
        awlen_latch            <= '0    ;
        awsize_latch           <= '0    ;
        awburst_latch          <= '0    ;
        awaddr_err             <= '0    ;
        wr_burst_err           <= '0    ;

        S_AXI_WREADY           <=  0    ;
        wr_beat_count          <=  0    ;
        write_ptr              <= '0    ;  
        wc_hs                  <= '0    ;
        wr_transfer_size_latch <= '0    ;
        wr_wrap_start_latch    <= '0    ;
        wr_wrap_end_latch      <= '0    ;
        wstrb_err              <= '0    ;
        
        S_AXI_BID              <= '0    ;
        S_AXI_BVALID           <= '0    ;
        S_AXI_BRESP            <= 2'b00 ;
    end
    else begin
        case(wr_state)
            WR_IDLE: begin
                S_AXI_AWREADY          <= '0;
                S_AXI_WREADY           <= '0;
                awc_hs                 <= '0;
                awid_latch             <= '0;
                awlen_latch            <= '0;
                awsize_latch           <= '0;
                awburst_latch          <= '0;
                write_ptr              <= '0;
                wr_transfer_size_latch <= '0;
                wr_wrap_start_latch    <= '0;
                wr_wrap_end_latch      <= '0;
                S_AXI_BID              <= '0;
                S_AXI_BRESP            <= '0;
                S_AXI_BVALID           <= '0;
                awaddr_err             <= '0;
                wr_burst_err           <= '0;
                wstrb_err              <= '0;
            end
            WR_WAIT: begin
                if(S_AXI_AWVALID) begin
                    S_AXI_AWREADY          <= 1'b1              ;
                    awc_hs                 <= 1'b1              ;
                    awid_latch             <= S_AXI_AWID        ;
                    awlen_latch            <= S_AXI_AWLEN       ;
                    awsize_latch           <= S_AXI_AWSIZE      ;
                    awburst_latch          <= S_AXI_AWBURST     ;
                    awaddr_latch           <= S_AXI_AWADDR      ;
                    write_ptr              <= S_AXI_AWADDR[4:2] ;
                    wr_transfer_size_latch <= wr_transfer_size  ;
                    wr_wrap_start_latch    <= wr_wrap_start     ;
                    wr_wrap_end_latch      <= wr_wrap_end       ;
                end
                S_AXI_WREADY <= 1'b1;
                if(S_AXI_WVALID) begin
                    wc_hs        <= 1'b1;
                end
            end
            WR_DATA: begin
                S_AXI_AWREADY <= 1'b0; // Pull down AWREADY 
                if(!(wstrb_err || awaddr_err || wr_burst_err) && wr_beat_count < awlen_latch + 1) begin
                    for (int i = 0; i < DATA_WIDTH/8; i++) begin
                        if (S_AXI_WSTRB[i])
                            regfile[write_ptr][8*i +: 8] <= S_AXI_WDATA[8*i +: 8];
                    end

                    wr_beat_count <= wr_beat_count + 1;

                    case(awburst_latch) // AWBURST handling
                        2'b00: write_ptr <= write_ptr;      // FIXED  
                        2'b01: begin
                            if(write_ptr >= awlen_latch) begin
                                awaddr_err <= 1'b1;
                            end
                            else begin
                                write_ptr <= write_ptr + 1;  // INCR
                            end
                        end
                        2'b10: begin                        // WRAP
                            if (write_ptr + 1 == wr_wrap_end_latch) begin
                                write_ptr <= wr_wrap_start_latch;
                            end
                            else begin
                                write_ptr <= write_ptr + 1;
                            end
                        end
                        2'b11:  wr_burst_err <= 1'b1;  // BURST ERROR
                    endcase
                end

                if(S_AXI_WSTRB == '0) begin
                    wstrb_err <= 1'b1;
                end

                if (wr_beat_count == 0) begin
                    if(!(awaddr_latch[1:0] == 2'b00)) begin
                        awaddr_err <= 1'b1;
                    end
                end

                if(wr_beat_count > 0) begin
                    if (write_ptr < awaddr_latch[ADDR_LSB +: ADDR_INDEX_W] || write_ptr > awaddr_latch[ADDR_LSB +: ADDR_INDEX_W] + (1 << ADDR_INDEX_W) - 1) begin
                        awaddr_err <=1'b1;
                    end
                end
            end

            WR_RESP: begin
                wr_beat_count <= '0;
                S_AXI_WREADY  <= 1'b0;
                S_AXI_BVALID  <= 1'b1;
                S_AXI_BID     <= awid_latch;

                S_AXI_BRESP  <= (awaddr_err)                ? 2'b11 :  // DECERR
                                (wstrb_err || wr_burst_err) ? 2'b10 :  // SLVERR
                                                              2'b00 ;  // OKAY
                if (S_AXI_BREADY && S_AXI_BVALID) begin
                    awc_hs        <= 1'b0;
                    wc_hs         <= 1'b0;
                    S_AXI_BVALID  <= 1'b0;
                    write_ptr     <= '0;
                end
            end
        endcase
    end
end

// Read-Path FSM
typedef enum logic [1:0] {
    RD_IDLE,    // IDLE STATE
    RD_WAIT,    // WAIT FOR HANDSHAKES
    RD_DATA     // PERFORM READ + RESPONSES
} rd_state_t;
rd_state_t rd_state, rd_next;

// Read Handshake Flag
logic ar_hs;
// Burst Registers
logic [7:0] rd_beat_count;
// Error Handling Registers
logic ar_err, r_burst_err;

always_comb begin
    rd_next = rd_state;
    case(rd_state)
        RD_IDLE: if (S_AXI_ARVALID)                               rd_next = RD_WAIT;
        RD_WAIT: if (ar_hs )                                      rd_next = RD_DATA;
        RD_DATA: if (rd_beat_count == 0 || ar_err || r_burst_err) rd_next = RD_IDLE;
    endcase
end

always_ff @(posedge ACLK or negedge ARESETN) begin
    if(!ARESETN) begin
        rd_state <= RD_IDLE;
    end
    else begin
        rd_state <= rd_next;
    end
end

// Read Pointer for Regfile
logic [ADDR_INDEX_W-1:0] read_ptr;
// Read Registers/Latches
logic [ADDR_WIDTH-1:0]  arid_latch    ;
logic [7:0]             arlen_latch   ;
logic [2:0]             arsize_latch  ;
logic [ADDR_WIDTH-1:0]  araddr_latch  ;
logic [1:0]             arburst_latch ;
logic                   rd_complete   ;
// WRAP Burst
logic [11:0] rd_transfer_size, rd_wrap_start, rd_transfer_size_latch, rd_wrap_start_latch, rd_wrap_end, rd_wrap_end_latch;
assign rd_transfer_size = (arlen_latch + 1)*(2**arsize_latch);
assign rd_wrap_start    = (S_AXI_ARADDR/ rd_transfer_size) * rd_transfer_size;
assign rd_wrap_end      = rd_wrap_start + rd_transfer_size;

always_ff @(posedge ACLK or negedge ARESETN) begin
    if(!ARESETN) begin
        S_AXI_ARREADY <=  0   ;
        S_AXI_RID     <= '0   ;
        S_AXI_RDATA   <= '0   ;
        S_AXI_RRESP   <= 2'b00;
        S_AXI_RLAST   <=  0   ;
        S_AXI_RVALID  <=  0   ;
        read_ptr      <= '0   ;
        ar_hs         <=  0   ;
    end
    else begin
        case(rd_state)
            RD_IDLE: begin
                S_AXI_ARREADY          <=  0;
                S_AXI_RLAST            <=  0;
                S_AXI_RVALID           <=  0;
                ar_hs                  <=  0;
                arid_latch             <= '0;
                arlen_latch            <= '0;
                arsize_latch           <= '0;
                araddr_latch           <= '0;
                r_burst_err            <= '0;
                ar_err                 <= '0;
                arburst_latch          <= '0;
                read_ptr               <= '0;
                rd_beat_count          <= '0;
                rd_transfer_size_latch <= '0;
                rd_wrap_start_latch    <= '0;
                rd_wrap_end_latch      <= '0;
            end
            
            RD_WAIT: begin
                S_AXI_ARREADY          <= 1'b1              ;
                ar_hs                  <= 1'b1              ;
                arid_latch             <= S_AXI_ARID        ;
                arlen_latch            <= S_AXI_ARLEN       ;
                araddr_latch           <= S_AXI_ARADDR      ;
                arsize_latch           <= S_AXI_ARSIZE      ;
                arburst_latch          <= S_AXI_ARBURST     ;
                read_ptr               <= S_AXI_ARADDR[4:2] ;
                rd_beat_count          <= arlen_latch + 1   ;
                rd_transfer_size_latch <= rd_transfer_size  ;
                rd_wrap_start_latch    <= rd_wrap_start     ;   
                rd_wrap_end_latch      <= rd_wrap_end       ;
            end

            RD_DATA: begin
                S_AXI_ARREADY          <= 1'b0;
                if (rd_beat_count == arlen_latch + 1 && !(araddr_latch[1:0] == 2'b00)) begin
                    ar_err <= 1'b1;
                    if (S_AXI_RREADY) begin
                        S_AXI_RVALID <= 1'b1;
                        S_AXI_RLAST  <= 1'b1;
                        S_AXI_RID    <= arid_latch;
                        S_AXI_RRESP  <= 2'b11;
                    end
                end
                else if (rd_beat_count == arlen_latch && (read_ptr < araddr_latch[4:2] || read_ptr > araddr_latch[4:2] + 7)) begin
                    ar_err <= 1'b1;
                    if (S_AXI_RREADY) begin
                        S_AXI_RVALID <= 1'b1;
                        S_AXI_RLAST  <= 1'b1;
                        S_AXI_RID    <= arid_latch;
                        S_AXI_RRESP  <= 2'b11;
                    end
                end
                else if (arburst_latch == 2'b11) begin
                    r_burst_err <= 1'b1;
                    if (S_AXI_RREADY) begin
                        S_AXI_RVALID <= 1'b1;
                        S_AXI_RLAST  <= 1'b1;
                        S_AXI_RID    <= arid_latch;
                        S_AXI_RRESP  <= 2'b01;
                    end
                end

                else begin
                    if(rd_beat_count > 1 && S_AXI_RREADY) begin
                        S_AXI_RVALID <= 1'b1;
                        S_AXI_RDATA  <= regfile[read_ptr];
                        S_AXI_RID    <= arid_latch;
                        case(arburst_latch)
                            2'b00: read_ptr <= read_ptr;        // FIXED
                            2'b01: 
                                if(read_ptr >= arlen_latch) begin
                                    ar_err <= 1'b1;
                                end
                                else begin 
                                read_ptr <= read_ptr + 1;    // INCR
                                end
                            2'b10:                              // WRAP
                                if (read_ptr + 1 == rd_wrap_end_latch) begin
                                    read_ptr <= rd_wrap_start_latch;
                                end
                                else begin
                                    read_ptr <= read_ptr + 1;
                                end
                        endcase
                        rd_beat_count <= rd_beat_count - 1;
                    end
                    else if (rd_beat_count == 1 && S_AXI_RREADY) begin
                        S_AXI_RVALID <= 1'b1;
                        S_AXI_RLAST  <= 1'b1;
                        S_AXI_RDATA  <= regfile[read_ptr];
                        S_AXI_RID    <= arid_latch;
                        S_AXI_RRESP  <= (ar_err)      ? 2'b11 :  // DECERR
                                        (r_burst_err) ? 2'b10 :  // SLVERR
                                                        2'b00 ;  // OKAY
                        rd_beat_count <= 0;
                    end
                end
            end
        endcase
    end
end

assign write_en = awc_hs && wc_hs;
assign read_en  = ar_hs;
endmodule