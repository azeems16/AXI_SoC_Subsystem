module dma_master #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH   = 4
)(
    // AXI-4 Style
    input  logic                      ACLK              ,
    input  logic                      ARESETN           ,

    //==============================
    // Write Address Channel
    //==============================
    output logic [ID_WIDTH-1:0]       M_AXI_AWID        ,
    output logic [ADDR_WIDTH-1:0]     M_AXI_AWADDR      ,
    output logic [7:0]                M_AXI_AWLEN       ,
    output logic [2:0]                M_AXI_AWSIZE      ,
    output logic [1:0]                M_AXI_AWBURST     ,
    output logic                      M_AXI_AWVALID     ,
    input  logic                      M_AXI_AWREADY     ,

    //==============================
    // Write Data Channel
    //==============================
    output logic [DATA_WIDTH-1:0]     M_AXI_WDATA       ,
    output logic [(DATA_WIDTH/8)-1:0] M_AXI_WSTRB       ,
    output logic                      M_AXI_WLAST       ,
    output logic                      M_AXI_WVALID      ,
    input  logic                      M_AXI_WREADY      ,

    //==============================
    // Write Response Channel
    //==============================
    input  logic [ID_WIDTH-1:0]       M_AXI_BID         ,
    input  logic [1:0]                M_AXI_BRESP       ,
    input  logic                      M_AXI_BVALID      ,
    output logic                      M_AXI_BREADY      ,

    //==============================
    // Read Address Channel
    //==============================
    output logic [ID_WIDTH-1:0]       M_AXI_ARID        ,
    output logic [ADDR_WIDTH-1:0]     M_AXI_ARADDR      ,
    output logic [7:0]                M_AXI_ARLEN       ,
    output logic [2:0]                M_AXI_ARSIZE      ,
    output logic [1:0]                M_AXI_ARBURST     ,
    output logic                      M_AXI_ARVALID     ,
    input  logic                      M_AXI_ARREADY     ,

    //==============================
    // Read Data Channel
    //==============================
    input  logic [ID_WIDTH-1:0]       M_AXI_RID         ,
    input  logic [DATA_WIDTH-1:0]     M_AXI_RDATA       ,
    input  logic [1:0]                M_AXI_RRESP       ,
    input  logic                      M_AXI_RLAST       ,
    input  logic                      M_AXI_RVALID      ,
    output logic                      M_AXI_RREADY      ,

    // CPU to Master to Slave Ports
    input logic [DATA_WIDTH-1:0]     src_reg            ,
    input logic [DATA_WIDTH-1:0]     dst_reg            ,
    input logic [DATA_WIDTH-1:0]     len_reg            ,
    input logic [DATA_WIDTH-1:0]     ctrl_reg           ,
    input logic [DATA_WIDTH-1:0]     status_reg         ,
    input logic [1:0]                burst_reg          ,

    output logic                     dma_done 
);

//======================================================================
// <Write Path FSM>: Start
//======================================================================
typedef enum logic [1:0] {
    IDLE    ,
    AWADDR  ,
    WDATA   ,
    BRESP
} wr_state_t;

wr_state_t wr_state, wr_next;

always_ff @ (posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) begin
        wr_state <= IDLE;
    end
    else begin
        wr_state <= wr_next;
    end
end

always_comb begin
    wr_next = wr_state;
    case(wr_state)
        IDLE   : if (ctrl_reg[CTRL_START_BIT]) wr_next = AWADDR;
        AWADDR : if (awc_hs)                   wr_next = WDATA;
        WDATA  : if (wc_hs && M_AXI_WLAST)     wr_next = BRESP;
        BRESP  : if (bc_hs)                    wr_next = IDLE;
        default:                               wr_next = IDLE;
    endcase
end

//======================================================================
// <DMA FIFO Instantiation>: Between Read & Write Path
//======================================================================
logic fifo_rd_en, fifo_wr_en;
logic fifo_empty, fifo_full;
logic [DATA_WIDTH-1:0] fifo_rd_data, fifo_wr_data;

dma_data_fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .DEPTH(16)
) u_dma_fifo (
    .clk      (ACLK)    ,
    .rst_n    (ARESETN) ,

    // Write side: from AXI read FSM
    .wr_en    (fifo_wr_en)  ,
    .wr_data  (fifo_wr_data),
    .full     (fifo_full)   ,

    // Read side: to AXI write FSM
    .rd_en    (fifo_rd_en)   ,
    .rd_data  (fifo_rd_data) ,
    .empty    (fifo_empty)
);

//======================================================================
// <Write Path Logic>: Start
//======================================================================
// Global Registers/Flags/Params
localparam logic [2:0] AWRSIZE_VAL     = $clog2(DATA_WIDTH/8);
localparam [1:0]       AXI_RESP_OKAY   = 2'b00;
localparam [1:0]       AXI_RESP_SLVERR = 2'b10;
localparam [1:0]       AXI_RESP_DECERR = 2'b11;
logic status_done_reg, status_err_reg;
logic wr_done_reg, rd_done_reg;
logic wr_err_reg, rd_err_reg;

// Write Registers/Flags/Params
localparam integer     BEAT_CNT_WIDTH  = $clog2(256); // = 8
logic awc_hs, wc_hs, bc_hs;

logic awvalid_reg, wvalid_reg, bready_reg;
logic [BEAT_CNT_WIDTH-1:0] w_beat_counter;


always_ff @ (posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) begin
        awc_hs          <= 0;
        wc_hs           <= 0;
        wr_state        <= IDLE;

        awvalid_reg     <= 0;
        wvalid_reg      <= 0;
        bready_reg      <= 0;
  
        fifo_rd_en      <= 0;
        w_beat_counter  <= 0;

        wr_done_reg     <= 0;
        wr_err_reg      <= 0;
    end
    else begin
        case(wr_state)
            IDLE: begin
                awc_hs         <= 0;
                wc_hs          <= 0;
                bc_hs          <= 0;

                awvalid_reg    <= 0;
                wvalid_reg     <= 0;
                bready_reg     <= 0;

                fifo_rd_en     <= 0;
                w_beat_counter <= 0;
                
                wr_done_reg    <= 0;
                wr_err_reg     <= 0;
            end

            AWADDR: begin
               wr_done_reg   <= 0;
               wr_err_reg    <= 0;

               M_AXI_AWADDR  <= dst_reg;
               M_AXI_AWLEN   <= len_reg;
               M_AXI_AWBURST <= burst_reg;
               M_AXI_AWSIZE  <= AWRSIZE_VAL;
               awvalid_reg   <= 1;
               
                if (awvalid_reg && M_AXI_AWREADY) begin
                    awc_hs         <= 1;
                    w_beat_counter <= 0;
                end
            end

            WDATA: begin            
                awc_hs        <= 0;
                awvalid_reg   <= 0;
                fifo_rd_en    <= 0;

                // Let data latch and stabilize prior to handshake
                if (!fifo_empty && !wvalid_reg) begin
                    M_AXI_WDATA  <= fifo_rd_data;
                    M_AXI_WLAST  <= (w_beat_counter == len_reg - 1);
                    M_AXI_WSTRB  <= '1;
                    wvalid_reg   <=  1;
                end

                // Handshake Detected, Send Beat
                if (wvalid_reg && M_AXI_WREADY) begin
                    wc_hs        <= 1;
                    fifo_rd_en   <= 1;
                    w_beat_counter <= w_beat_counter + 1;
                    wvalid_reg   <= 0;
                end
            end

            BRESP: begin
                wc_hs      <= 0;
                bready_reg <= 1;

                if (bready_reg && M_AXI_BVALID) begin
                    bc_hs      <= 1;
                    bready_reg <= 0;
                    if (M_AXI_BRESP != AXI_RESP_OKAY) begin
                        wr_done_reg     <= 1;
                        wr_err_reg      <= 1;
                    end
                    else begin
                        wr_done_reg     <= 1;
                        wr_err_reg      <= 0;
                    end
                end
            end
        endcase
    end
end

assign M_AXI_AWVALID = awvalid_reg;
assign M_AXI_WVALID  = wvalid_reg ;
assign M_AXI_BREADY  = bready_reg ;

assign status_reg[STATUS_DONE_BIT] = rd_done_reg && wr_done_reg;
assign status_reg[STATUS_ERR_BIT ] = rd_err_reg || wr_err_reg;

//======================================================================
// <Read Path FSM>: Start
//======================================================================
typedef enum logic [1:0] {
    IDLE    , 
    ARADDR  ,
    RDATA
} rd_state_t;

rd_state_t rd_state, rd_next;

always_ff @ (posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) begin
        rd_state <= IDLE;
    end
    else begin
        rd_state <= rd_next;
    end
end

always_comb begin
    rd_next = rd_state; 
    case(rd_state) 
        IDLE    : if (ctrl_reg[CTRL_START_BIT]) rd_next = ARADDR;
        ARADDR  : if (ar_hs)                    rd_next = RDATA;
        RDATA   : if (M_AXI_RLAST)              rd_next = IDLE;
        default :                               rd_next = IDLE;
    endcase
end

//======================================================================
// <Read Path Logic>: Start
//======================================================================
logic ar_hs;

logic arvalid_reg, rready_reg;
always_ff @ (posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) begin
        ar_hs <= 0;
        
        rd_done_reg <= 0;
        rd_err_reg  <= 0;
    end
    else begin
        case(rd_state)
            IDLE: begin
                ar_hs       <= 0;

                arvalid_reg <= 0;
                rready_reg  <= 0;

                fifo_wr_en  <= 0;

                rd_done_reg <= 0;
                rd_err_reg  <= 0;
            end
            ARADDR: begin
                rd_done_reg     <= 0;
                rd_err_reg      <= 0;
                M_AXI_ARADDR    <= src_reg;
                M_AXI_ARLEN     <= len_reg;
                M_AXI_ARSIZE    <= AWRSIZE_VAL;
                M_AXI_ARBURST   <= burst_reg;
                arvalid_reg     <= 1;

                if (M_AXI_ARREADY && arvalid_reg) begin
                    ar_hs          <= 1;
                end
            end
            RDATA: begin
                ar_hs       <= 0;
                arvalid_reg <= 0;
                rready_reg  <= 1;

                if (rready_reg && M_AXI_RVALID && !fifo_full) begin
                    fifo_wr_en   <= 1;
                    fifo_wr_data <= M_AXI_RDATA;
                    if(M_AXI_RLAST) begin
                        if (M_AXI_RRESP != AXI_RESP_OKAY) begin
                            rd_done_reg    <= 1;
                            rd_err_reg     <= 1;
                        end
                        else begin
                            rd_done_reg    <= 1;
                            rd_err_reg     <= 0;
                        end
                    end
                end
                else begin
                    fifo_wr_en   <= 0;
                end                
            end
        endcase
    end
end

assign M_AXI_ARVALID = arvalid_reg;
assign M_AXI_RREADY  = rready_reg ;

//======================================================================
// <IRQ logic>: Start
//======================================================================
assign dma_done = rd_done_reg && wr_done_reg;
endmodule