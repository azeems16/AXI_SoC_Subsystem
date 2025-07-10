interface axi4_intf #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
);

// Global Signals
logic ACLK;
logic ARESETN;

// AW Channel
logic [ADDR_WIDTH-1:0] AWADDR ;
logic [7:0]            AWLEN  ;
logic [2:0]            AWSIZE ;
logic [1:0]            AWBURST;
logic                  AWVALID;
logic                  AWREADY;

// W Channel
logic [DATA_WIDTH-1:0]     WDATA  ;
logic [(DATA_WIDTH/8)-1:0] WSTRB  ;
logic                      WLAST  ;
logic                      WVALID ;
logic                      WREADY ;

// B Channel
logic [1:0] BRESP  ;
logic       BVALID ;
logic       BREADY ;

// AR Channel
logic [ADDR_WIDTH-1:0] ARADDR  ;
logic [7:0]            ARLEN   ;
logic [2:0]            ARSIZE  ;
logic [1:0]            ARBURST ;
logic                  ARVALID ;
logic                  ARREADY ;

// R Channel
logic [DATA_WIDTH-1:0] RDATA  ;
logic [1:0]            RRESP  ;
logic                  RLAST  ;
logic                  RVALID ;
logic                  RREADY ;

modport monitor (
    input AWADDR, AWLEN, AWSIZE, AWBURST, AWVALID, AWREADY,
    input WDATA, WSTRB, WLAST, WVALID, WREADY,
    input BRESP, BVALID, BREADY,
    input ARADDR, ARLEN, ARSIZE, ARBURST, ARVALID, ARREADY,
    input RDATA, RRESP, RLAST, RVALID, RREADY
);

modport driver (
    input ACLK, ARESETN,
    input AWREADY, 
    input WREADY,
    input BVALID,
    input ARREADY,
    input RVALID, RLAST, 

    output AWADDR, AWLEN, AWSIZE, AWBURST, AWVALID,
    output WDATA, WSTRB, WVALID, WLAST, 
    output BREADY,
    output ARADDR, ARLEN, ARSIZE, ARBURST, ARVALID,
    output RREADY
);

modport DUT (
    input  ACLK, ARESETN,
    input  AWADDR, AWLEN, AWSIZE, AWBURST, AWVALID,
    input  WDATA, WSTRB, WVALID, WLAST,
    input  BREADY,
    input  ARADDR, ARLEN, ARSIZE, ARBURST, ARVALID,
    input  RREADY,

    output AWREADY,
    output WREADY,
    output BVALID, BRESP,
    output ARREADY,
    output RVALID, RDATA, RRESP, RLAST
);

endinterface