class soc_timer_coverage;
localparam ADDR_WIDTH = 32;
localparam DATA_WIDTH = 32;
logic                  ACLK        ;
logic                  ARESETN     ;
logic                  AWVALID     ;
logic                  AWREADY     ;
logic [ADDR_WIDTH-1:0] AWADDR      ;
logic                  WVALID      ;
logic                  WREADY      ;
logic [DATA_WIDTH-1:0] WDATA       ;
logic                  ARVALID     ;
logic                  ARREADY     ;
logic [ADDR_WIDTH-1:0] ARADDR      ;
logic                  RVALID      ;
logic                  RREADY      ;
logic [DATA_WIDTH-1:0] RDATA       ;
logic                  irq         ;

logic [31:0] cvrg_control_reg;
logic [31:0] cvrg_irq_reg;
logic [31:0] cvrg_clear_reg;

covergroup timer_cg @ (posedge ACLK);
    option.per_instance = 1;
    coverpoint AWADDR iff (AWVALID && AWREADY) {
        bins load_reg        = {32'h00};
        bins control_reg     = {32'h04};
        bins int_clear_reg   = {32'h10};
        illegal_bins invalid = default;
    }

    coverpoint ARADDR iff (ARVALID && ARREADY) {
        bins control_reg     = {32'h04};
        bins counter_reg     = {32'h08};
        bins int_status_reg  = {32'h0C};
        illegal_bins invalid = default;
    }
    //enable
    coverpoint cvrg_control_reg[0] {
        bins disabled = {0};
        bins enabled  = {1};
    }
    //auto reload
    coverpoint cvrg_control_reg[1] {
        bins disabled = {0};
        bins enabled  = {1};
    }
    //mask
    coverpoint cvrg_control_reg[2] {
        bins disabled = {0};
        bins enabled  = {1};
    }

    coverpoint cvrg_irq_reg[0] {
        bins no_irq      = {0};
        bins interrupted = {1};
    }

    coverpoint cvrg_clear_reg[0] {
        bins uncleared = {0};
        bins cleared   = {1};
    }

    coverpoint irq{
        bins inactive = {0};
        bins active   = {1};
    }

    // cross cvrg_control_reg[2:0], cvrg_irq_reg[0];
    // cross cvrg_control_reg[0], cvrg_control_reg[1], cvrg_control_reg[2];

endgroup

function new(input clk);
    this.ACLK = clk;
    timer_cg = new();
endfunction

function drive_sample(
    input logic                  ARESETN,
    input logic                  AWVALID,
    input logic                  AWREADY,
    input logic [ADDR_WIDTH-1:0] AWADDR ,
    input logic                  WVALID ,
    input logic                  WREADY ,
    input logic [DATA_WIDTH-1:0] WDATA  ,
    input logic                  ARVALID,
    input logic                  ARREADY,
    input logic [ADDR_WIDTH-1:0] ARADDR ,
    input logic                  RVALID ,
    input logic                  RREADY ,
    input logic [DATA_WIDTH-1:0] RDATA  ,
    input logic                  irq         
);
    this.ARESETN = ARESETN;
    this.AWVALID = AWVALID;
    this.AWREADY = AWREADY;
    this.AWADDR  = AWADDR ;
    this.WVALID  = WVALID ;
    this.WREADY  = WREADY ;
    this.WDATA   = WDATA  ;
    this.ARVALID = ARVALID;
    this.ARREADY = ARREADY;
    this.ARADDR  = ARADDR ;
    this.RVALID  = RVALID ;
    this.RREADY  = RREADY ;
    this.RDATA   = RDATA  ;
    this.irq     = irq    ;
    timer_cg.sample();
endfunction

endclass