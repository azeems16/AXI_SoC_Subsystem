module dma_slave #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    // AXI-Lite Style
    input  logic                      ACLK              ,
    input  logic                      ARESETN           ,

    // Write address channel
    input  logic [ADDR_WIDTH-1:0]     S_AXI_AWADDR      ,
    input  logic                      S_AXI_AWVALID     ,
    output logic                      S_AXI_AWREADY     ,

    // Write data channel
    input  logic [DATA_WIDTH-1:0]     S_AXI_WDATA       ,
    input  logic [(DATA_WIDTH/8)-1:0] S_AXI_WSTRB       ,
    input  logic                      S_AXI_WVALID      ,
    output logic                      S_AXI_WREADY      ,

    // Write response channel
    output logic [1:0]                S_AXI_BRESP       ,
    output logic                      S_AXI_BVALID      ,
    input  logic                      S_AXI_BREADY      ,

    // Read address channel
    input  logic [ADDR_WIDTH-1:0]     S_AXI_ARADDR      ,
    input  logic                      S_AXI_ARVALID     ,
    output logic                      S_AXI_ARREADY     ,

    // Read data channel
    output logic [DATA_WIDTH-1:0]     S_AXI_RDATA       ,
    output logic [1:0]                S_AXI_RRESP       ,
    output logic                      S_AXI_RVALID      ,
    input  logic                      S_AXI_RREADY

    // CPU to Master to Slave Ports
    output logic [DATA_WIDTH-1:0]     src_reg           ,
    output logic [DATA_WIDTH-1:0]     dst_reg           ,
    output logic [DATA_WIDTH-1:0]     len_reg           ,
    output logic [DATA_WIDTH-1:0]     ctrl_reg          ,
    output logic [DATA_WIDTH-1:0]     status_reg        ,
    output logic [1:0]                burst_reg         
);

//======================================================================
// <AXI-Lite: CPU (Master) to DMA (Slave)>: Start
//======================================================================

function automatic [DATA_WIDTH-1:0] reg_strb_write(
    input logic [(DATA_WIDTH/8)-1:0] w_strb   ,
    input logic [DATA_WIDTH-1:0    ] register ,
    input logic [DATA_WIDTH-1:0    ] w_data   
);
    logic [DATA_WIDTH-1:0  ] out_reg;
    logic [7:0]              byte_result;

    for(int i = 0; i < (DATA_WIDTH/8) ; i++) begin
        byte_result = w_strb[i] ? w_data[(i*8) +: 8] : register[(i*8) +: 8];
        out_reg[(i*8) +: 8] = byte_result;
    end
    reg_strb_write = out_reg;
endfunction

logic [DATA_WIDTH-1:0] s_wdata_reg;
logic [ADDR_WIDTH-1:0] s_awaddr_reg, s_araddr_reg;
logic [DATA_WIDTH-1:0] src_reg, dst_reg, len_reg, ctrl_reg, status_reg;
logic [1:0] burst_reg;
logic awc_hs, wc_hs, arc_hs;
logic s_write_en;
logic [1:0] bresp, rresp;
assign s_write_en = awc_hs & wc_hs;
always @ (posedge ACLK or negedge ARESETN) begin
    // Reset Logic
    if (!ARESETN) begin
        s_wdata_reg  <= '0;
        s_awaddr_reg <= '0;
        s_araddr_reg <= '0;
        
        awc_hs       <=  0;
        wc_hs        <=  0;
        arc_hs       <=  0;
        
        bresp        <= '0;
        rresp        <= '0;

        src_reg      <= '0;
        dst_reg      <= '0;
        len_reg      <= '0;
        ctrl_reg     <= '0;
        status_reg   <= '0;
    end
    else begin
    // Write Path
        if (S_AXI_AWVALID) begin
            S_AXI_AWREADY <= 1;
            awc_hs        <= 1;
            s_awaddr_reg  <= S_AXI_AWADDR;
        end

        if (S_AXI_WVALID) begin
            S_AXI_WREADY <= 1;
            wc_hs        <= 1;
            s_wdata_reg  <= S_AXI_WDATA;
        end

        // Pull Downs
        if (awc_hs) begin
            S_AXI_AWREADY <= 0;
        end

        if (wc_hs) begin
            S_AXI_WREADY <= 0;
        end

        if (BREADY && BVALID) begin          
            BVALID <= 0;        
            awc_hs <= 0;
            wc_hs  <= 0;
        end

        if (s_write_en) begin
            bresp <= 2'b00;
            case(s_awaddr_reg)
                SRC_ADDR: src_reg    <= reg_strb_write(S_AXI_WSTRB, src_reg    , s_wdata_reg);
                DST_ADDR: dst_reg    <= reg_strb_write(S_AXI_WSTRB, dst_reg    , s_wdata_reg);
                LENGTH  : len_reg    <= reg_strb_write(S_AXI_WSTRB, len_reg    , s_wdata_reg);
                CONTROL : ctrl_reg   <= reg_strb_write(S_AXI_WSTRB, ctrl_reg   , s_wdata_reg);
                STATUS  : status_reg <= reg_strb_write(S_AXI_WSTRB, status_reg , s_wdata_reg);
                BURST   : burst_reg  <= s_wdata_reg[1:0];
                default:
                    bresp <= 2'b10; // SLVERR
            endcase
            awc_hs       <= 0;  
            wc_hs        <= 0;  
            BVALID       <= 1;  
            S_AXI_BRESP  <= bresp;
        end
    // Read Path
        if (S_AXI_ARVALID) begin
            S_AXI_ARREADY <= 1;
            arc_hs        <= 1;
            s_araddr_reg  <= S_AXI_ARADDR;
        end

        if (arc_hs && S_AXI_RREADY) begin
            rresp        <= '0;
            S_AXI_RVALID <=  1;

            case(s_araddr_reg)
                SRC_ADDR: begin 
                    S_AXI_RDATA <= src_reg;                    
                end
                DST_ADDR: begin
                    S_AXI_RDATA <= dst_reg;
                end
                LENGTH: begin
                    S_AXI_RDATA <= len_reg;
                end
                STATUS: begin
                    S_AXI_RDATA <= status_reg;
                end
                BURST: begin
                    S_AXI_RDATA <= burst_reg;
                end
                default: begin
                    rresp <= 2'b10; // SLVERR
                    S_AXI_RDATA <= '0;
                end
            endcase
            S_AXI_RRESP  <= rresp;
            arc_hs <= 0;
        end

        if(arc_hs) begin
            S_AXI_ARREADY <= 0;
        end

        if (S_AXI_RREADY && S_AXI_RVALID) begin
            S_AXI_RVALID <= 0;
        end
    end
end
endmodule
