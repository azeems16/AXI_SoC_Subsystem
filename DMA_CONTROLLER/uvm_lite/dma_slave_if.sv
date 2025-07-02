interface axi_lite_if #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
);
    logic                      ACLK;
    logic                      ARESETN;

    // Write Address Channel
    logic [ADDR_WIDTH-1:0]     AWADDR;
    logic                      AWVALID;
    logic                      AWREADY;

    // Write Data Channel
    logic [DATA_WIDTH-1:0]     WDATA;
    logic [(DATA_WIDTH/8)-1:0] WSTRB;
    logic                      WVALID;
    logic                      WREADY;

    // Write Response Channel
    logic [1:0]                BRESP;
    logic                      BVALID;
    logic                      BREADY;

    // Read Address Channel
    logic [ADDR_WIDTH-1:0]     ARADDR;
    logic                      ARVALID;
    logic                      ARREADY;

    // Read Data Channel
    logic [DATA_WIDTH-1:0]     RDATA;
    logic [1:0]                RRESP;
    logic                      RVALID;
    logic                      RREADY;

    modport tb (
        output ACLK  , ARESETN,
               AWADDR, AWVALID, 
               WDATA , WSTRB  , WVALID,
               BREADY,
               ARADDR, ARVALID, 
               RREADY,

        input  AWREADY, 
               WREADY , 
               BVALID , BRESP, 
               ARREADY, 
               RDATA  , RRESP, RVALID 
    );

    modport drv (
        output AWREADY, 
               WREADY , 
               BVALID , BRESP, 
               ARREADY, 
               RDATA  , RRESP, RVALID,

        input  ACLK  , ARESETN,
               AWADDR, AWVALID, 
               WDATA , WSTRB  , WVALID,
               BREADY,
               ARADDR, ARVALID, 
               RREADY
    );

    modport mon (
        input  ACLK     , ARESETN ,
               AWADDR   , AWVALID , AWREADY,
               WDATA    , WSTRB   , WVALID , WREADY,
               BVALID   , BRESP   , BREADY ,
               ARADDR   , ARVALID , ARREADY,
               RDATA    , RRESP   , RVALID , RREADY
    );
endinterface
