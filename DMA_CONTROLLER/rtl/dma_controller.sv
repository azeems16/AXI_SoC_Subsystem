module dma_controller #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH   = 4
)(
    input  wire                      ACLK               ,
    input  wire                      ARESETN            ,       

    // --------------------------------------
    // AXI-Lite Slave Interface (Config)
    // --------------------------------------
    input  wire [ADDR_WIDTH-1:0]     S_AXI_AWADDR       ,
    input  wire                      S_AXI_AWVALID      ,
    output wire                      S_AXI_AWREADY      ,   

    input  wire [DATA_WIDTH-1:0]     S_AXI_WDATA        ,
    input  wire [(DATA_WIDTH/8)-1:0] S_AXI_WSTRB        ,
    input  wire                      S_AXI_WVALID       ,
    output wire                      S_AXI_WREADY       ,   

    output wire [1:0]                S_AXI_BRESP        ,
    output wire                      S_AXI_BVALID       ,
    input  wire                      S_AXI_BREADY       ,   

    input  wire [ADDR_WIDTH-1:0]     S_AXI_ARADDR       ,
    input  wire                      S_AXI_ARVALID      ,
    output wire                      S_AXI_ARREADY      ,   

    output wire [DATA_WIDTH-1:0]     S_AXI_RDATA        ,
    output wire [1:0]                S_AXI_RRESP        ,
    output wire                      S_AXI_RVALID       ,
    input  wire                      S_AXI_RREADY       ,   

    // --------------------------------------
    // AXI4 Master Interface (Burst Engine)
    // --------------------------------------
    output wire [ID_WIDTH-1:0]       M_AXI_AWID         ,
    output wire [ADDR_WIDTH-1:0]     M_AXI_AWADDR       ,
    output wire [7:0]                M_AXI_AWLEN        ,
    output wire [2:0]                M_AXI_AWSIZE       ,
    output wire [1:0]                M_AXI_AWBURST      ,
    output wire                      M_AXI_AWVALID      ,
    input  wire                      M_AXI_AWREADY      ,   

    output wire [DATA_WIDTH-1:0]     M_AXI_WDATA        ,
    output wire [(DATA_WIDTH/8)-1:0] M_AXI_WSTRB        ,
    output wire                      M_AXI_WLAST        ,
    output wire                      M_AXI_WVALID       ,
    input  wire                      M_AXI_WREADY       ,   

    input  wire [ID_WIDTH-1:0]       M_AXI_BID          ,
    input  wire [1:0]                M_AXI_BRESP        ,
    input  wire                      M_AXI_BVALID       ,
    output wire                      M_AXI_BREADY       ,   

    output wire [ID_WIDTH-1:0]       M_AXI_ARID         ,
    output wire [ADDR_WIDTH-1:0]     M_AXI_ARADDR       ,
    output wire [7:0]                M_AXI_ARLEN        ,
    output wire [2:0]                M_AXI_ARSIZE       ,
    output wire [1:0]                M_AXI_ARBURST      ,
    output wire                      M_AXI_ARVALID      ,
    input  wire                      M_AXI_ARREADY      ,   

    input  wire [ID_WIDTH-1:0]       M_AXI_RID          ,
    input  wire [DATA_WIDTH-1:0]     M_AXI_RDATA        ,
    input  wire [1:0]                M_AXI_RRESP        ,
    input  wire                      M_AXI_RLAST        ,
    input  wire                      M_AXI_RVALID       ,
    output wire                      M_AXI_RREADY       ,

    // --------------------------------------
    // Interrupt
    // --------------------------------------
    output wire                   irq_out
);

logic [DATA_WIDTH-1:0] src_reg_wire, dst_reg_wire, len_reg_wire, ctrl_reg_wire, status_reg_wire;
logic [1:0]            burst_reg_wire;
logic dma_done, irq_en;

assign irq_en  = ctrl_reg_wire[CTRL_IRQ_EN_BIT];
assign irq_out = irq_en ? dma_done : 1'b0;

dma_slave u_dma_slave (
    .ACLK           (ACLK           ) , 
    .ARESETN        (ARESETN        ) , 
    .S_AXI_AWADDR   (S_AXI_AWADDR   ) , 
    .S_AXI_AWVALID  (S_AXI_AWVALID  ) , 
    .S_AXI_AWREADY  (S_AXI_AWREADY  ) , 
    .S_AXI_WDATA    (S_AXI_WDATA    ) , 
    .S_AXI_WSTRB    (S_AXI_WSTRB    ) , 
    .S_AXI_WVALID   (S_AXI_WVALID   ) , 
    .S_AXI_WREADY   (S_AXI_WREADY   ) , 
    .S_AXI_BRESP    (S_AXI_BRESP    ) , 
    .S_AXI_BVALID   (S_AXI_BVALID   ) , 
    .S_AXI_BREADY   (S_AXI_BREADY   ) , 
    .S_AXI_ARADDR   (S_AXI_ARADDR   ) , 
    .S_AXI_ARVALID  (S_AXI_ARVALID  ) , 
    .S_AXI_ARREADY  (S_AXI_ARREADY  ) , 
    .S_AXI_RDATA    (S_AXI_RDATA    ) , 
    .S_AXI_RRESP    (S_AXI_RRESP    ) , 
    .S_AXI_RVALID   (S_AXI_RVALID   ) , 
    .S_AXI_RREADY   (S_AXI_RREADY   ) , 
    .src_reg        (src_reg_wire   ) ,
    .dst_reg        (dst_reg_wire   ) ,
    .len_reg        (len_reg_wire   ) ,
    .ctrl_reg       (ctrl_reg_wire  ) ,
    .burst_reg      (burst_reg_wire ) ,
    .status_reg     (status_reg_wire) ,
);

dma_master u_dma_master (
    .ACLK           (ACLK),
    .ARESETN        (ARESETN),

    .M_AXI_AWID     (M_AXI_AWID),
    .M_AXI_AWADDR   (M_AXI_AWADDR),
    .M_AXI_AWLEN    (M_AXI_AWLEN),
    .M_AXI_AWSIZE   (M_AXI_AWSIZE),
    .M_AXI_AWBURST  (M_AXI_AWBURST),
    .M_AXI_AWVALID  (M_AXI_AWVALID),
    .M_AXI_AWREADY  (M_AXI_AWREADY),

    .M_AXI_WDATA    (M_AXI_WDATA),
    .M_AXI_WSTRB    (M_AXI_WSTRB),
    .M_AXI_WLAST    (M_AXI_WLAST),
    .M_AXI_WVALID   (M_AXI_WVALID),
    .M_AXI_WREADY   (M_AXI_WREADY),

    .M_AXI_BID      (M_AXI_BID),
    .M_AXI_BRESP    (M_AXI_BRESP),
    .M_AXI_BVALID   (M_AXI_BVALID),
    .M_AXI_BREADY   (M_AXI_BREADY),

    .M_AXI_ARID     (M_AXI_ARID),
    .M_AXI_ARADDR   (M_AXI_ARADDR),
    .M_AXI_ARLEN    (M_AXI_ARLEN),
    .M_AXI_ARSIZE   (M_AXI_ARSIZE),
    .M_AXI_ARBURST  (M_AXI_ARBURST),
    .M_AXI_ARVALID  (M_AXI_ARVALID),
    .M_AXI_ARREADY  (M_AXI_ARREADY),

    .M_AXI_RID      (M_AXI_RID),
    .M_AXI_RDATA    (M_AXI_RDATA),
    .M_AXI_RRESP    (M_AXI_RRESP),
    .M_AXI_RLAST    (M_AXI_RLAST),
    .M_AXI_RVALID   (M_AXI_RVALID)   ,
    .M_AXI_RREADY   (M_AXI_RREADY)   ,

    .src_reg        (src_reg_wire   ) ,
    .dst_reg        (dst_reg_wire   ) ,
    .len_reg        (len_reg_wire   ) ,
    .ctrl_reg       (ctrl_reg_wire  ) ,
    .burst_reg      (burst_reg_wire ) ,
    .status_reg     (status_reg_wire) ,

    .dma_done       (dma_done)
);



endmodule