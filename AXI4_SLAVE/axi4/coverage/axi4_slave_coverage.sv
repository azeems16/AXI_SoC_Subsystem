class axi4_slave_coverage;

localparam integer DATA_WIDTH = 32;

logic ACLK;

// AW-Channel
logic awready;
logic awvalid;
logic [1:0] awburst;

// W-Channel
logic [(DATA_WIDTH/8)-1:0] wstrb;
logic wvalid;
logic wready;
logic wlast;

// B-Channel
logic [1:0] bresp;
logic bvalid;
logic bready;

// AR-Channel
logic arvalid;
logic arready;
logic [1:0] arburst;

// R-Channel
logic [1:0] rresp;
logic rvalid;
logic rready;
logic rlast;

covergroup axi4_slave_cg @ (posedge ACLK);
    option.per_instance = 1;
    //Handshake Crosses
    coverpoint awready {bins on = {1}; bins off = {0};}
    coverpoint awvalid {bins on = {1}; bins off = {0};}
    aw_cross: cross awready, awvalid;
    
    coverpoint wready {bins on   = {1}; bins off     = {0};}
    coverpoint wvalid {bins on   = {1}; bins off     = {0};}
    coverpoint wlast  {bins last = {1}; bins notlast = {0};}
    w_cross: cross wready, wvalid, wlast {
        bins last_handshake = binsof(wvalid) intersect {1} &&
                              binsof(wready) intersect {1} &&
                              binsof(wlast ) intersect {1};
    }
    
    coverpoint bready {bins on = {1}; bins off = {0};}
    coverpoint bvalid {bins on = {1}; bins off = {0};}
    b_cross: cross bready, bvalid;
    
    coverpoint arready {bins on = {1}; bins off = {0};}
    coverpoint arvalid {bins on = {1}; bins off = {0};}
    ar_cross: cross arready, arvalid;
    
    coverpoint rready {bins on   = {1}; bins off     = {0};}
    coverpoint rvalid {bins on   = {1}; bins off     = {0};}
    coverpoint rlast  {bins last = {1}; bins notlast = {0};}
    r_cross: cross rready, rvalid, rlast {
        bins last_handshake = binsof(rready) intersect {1} &&
                              binsof(rvalid) intersect {1} &&
                              binsof(rlast ) intersect {1};
    }

    // Bursts and Responses
    coverpoint bresp {
        bins okay       = {2'b00};
        bins slverr     = {2'b04};
        bins invalid    = {2'b10};
        bins awaddr_err = {2'b11};
    }

    coverpoint rresp {
        bins okay       = {2'b00};
        bins slverr     = {2'b01};
        bins invalid    = {2'b10};
        bins awaddr_err = {2'b11};
    }

    coverpoint awburst {
        bins fixed       = {2'b00};
        bins incr        = {2'b01};
        bins wrap        = {2'b10};
        bins invalid     = {2'b11};
    }

    coverpoint wstrb iff (wvalid && wready);
endgroup

function new(input logic clk);
    this.ACLK = clk;
    axi4_slave_cg = new();
endfunction

function void drive_sample(
    input logic                      awready ,
    input logic                      awvalid ,
    input logic [1:0]                awburst ,
    input logic [(DATA_WIDTH/8)-1:0] wstrb   ,
    input logic                      wvalid  ,
    input logic                      wready  ,
    input logic                      wlast   ,
    input logic [1:0]                bresp   ,
    input logic                      bvalid  ,
    input logic                      bready  ,
    input logic                      arvalid ,
    input logic                      arready ,
    input logic [1:0]                arburst ,
    input logic [1:0]                rresp   ,
    input logic                      rvalid  ,
    input logic                      rready  ,
    input logic                      rlast   
);
    this.awready = awready ;
    this.awvalid = awvalid ;
    this.awburst = awburst ;
    this.wstrb   = wstrb   ;
    this.wvalid  = wvalid  ;
    this.wready  = wready  ;
    this.wlast   = wlast   ;
    this.bresp   = bresp   ;
    this.bvalid  = bvalid  ;
    this.bready  = bready  ;
    this.arvalid = arvalid ;
    this.arready = arready ;
    this.arburst = arburst ;
    this.rresp   = rresp   ;
    this.rvalid  = rvalid  ;
    this.rready  = rready  ;
    this.rlast   = rlast   ;
    axi4_slave_cg.sample();
endfunction

endclass