module axi4_slave_sva #(
    parameter integer ID_WIDTH   = 4  ,
    parameter integer ADDR_WIDTH = 32 ,
    parameter integer DATA_WIDTH = 32
)(
    input                      ACLK           ,
    input                      ARESETN        ,
    input [ID_WIDTH-1:0]       S_AXI_AWID     ,
    input [ADDR_WIDTH-1:0]     S_AXI_AWADDR   ,
    input [7:0]                S_AXI_AWLEN    ,
    input [2:0]                S_AXI_AWSIZE   ,
    input [1:0]                S_AXI_AWBURST  ,
    input                      S_AXI_AWVALID  ,
    input                      S_AXI_AWREADY  ,
    input [DATA_WIDTH-1:0]     S_AXI_WDATA    ,
    input [(DATA_WIDTH/8)-1:0] S_AXI_WSTRB    ,
    input                      S_AXI_WLAST    ,
    input                      S_AXI_WVALID   ,
    input                      S_AXI_WREADY   ,
    input [ID_WIDTH-1:0]       S_AXI_BID      ,
    input [1:0]                S_AXI_BRESP    ,
    input                      S_AXI_BVALID   ,
    input                      S_AXI_BREADY   ,
    input [ID_WIDTH-1:0  ]     S_AXI_ARID     ,
    input [ADDR_WIDTH-1:0]     S_AXI_ARADDR   ,
    input [7:0]                S_AXI_ARLEN    ,
    input [2:0]                S_AXI_ARSIZE   ,
    input [1:0]                S_AXI_ARBURST  ,
    input                      S_AXI_ARVALID  ,
    input                      S_AXI_ARREADY  ,
    input [ID_WIDTH-1:0  ]     S_AXI_RID      ,
    input [DATA_WIDTH-1:0]     S_AXI_RDATA    ,
    input [1:0]                S_AXI_RRESP    ,
    input                      S_AXI_RLAST    ,
    input                      S_AXI_RVALID   ,
    input                      S_AXI_RREADY   ,
    input                      write_en       ,
    input                      read_en        
);

// TODO: Assertions compile but fire incorrectly. Confirm waveform-verified behavior.

property invalid_awburst;
    @ (posedge ACLK) disable iff (!ARESETN)
    (S_AXI_AWVALID && S_AXI_AWREADY) |-> !(S_AXI_AWBURST == 2'b11);
endproperty

property invalid_arburst;
    @ (posedge ACLK) disable iff (!ARESETN)
    (S_AXI_ARVALID && S_AXI_ARREADY) |-> !(S_AXI_ARBURST == 2'b11);
endproperty

property last_w_beat;
    @ (posedge ACLK) disable iff (!ARESETN)
    (S_AXI_WLAST) |-> (S_AXI_WREADY && S_AXI_WVALID);
endproperty

property last_r_beat;
    @ (posedge ACLK) disable iff (!ARESETN)
    (S_AXI_RLAST) |-> (S_AXI_RREADY && S_AXI_RVALID);
endproperty

property valid_wstrb;
    @ (posedge ACLK) disable iff (!ARESETN)
    (S_AXI_WVALID && S_AXI_WREADY) |-> !(S_AXI_WSTRB == '0);
endproperty

property valid_awlen;
    @(posedge ACLK) disable iff (!ARESETN)
    (S_AXI_AWVALID && S_AXI_AWREADY) |-> (S_AXI_AWLEN <= 8'd255);
endproperty

property valid_arlen;
    @(posedge ACLK) disable iff (!ARESETN)
    (S_AXI_ARVALID && S_AXI_ARREADY) |-> (S_AXI_ARLEN <= 8'd255);
endproperty

property stable_wvalid;
  @(posedge ACLK) disable iff (!ARESETN)
  S_AXI_WVALID && !S_AXI_WREADY |=> $stable(S_AXI_WDATA);
endproperty

property stable_awaddr;
  @(posedge ACLK) disable iff (!ARESETN)
  S_AXI_AWVALID && !S_AXI_AWREADY |=> $stable(S_AXI_AWADDR);
endproperty

property stable_araddr;
  @(posedge ACLK) disable iff (!ARESETN)
  S_AXI_ARVALID && !S_AXI_ARREADY |=> $stable(S_AXI_ARADDR);
endproperty

property w_before_b;
    @(posedge ACLK) disable iff (!ARESETN)
    !write_en |-> !S_AXI_BVALID;
endproperty

property ar_before_r;
    @(posedge ACLK) disable iff (!ARESETN)
    !read_en |-> !S_AXI_RVALID;
endproperty

// In practice this should be $fatal or $error but due to this project being validated through EDAPlayground we use $warning to obtain waveforms
assert property (invalid_awburst)
  else $warning("ASSERTION FAILED: invalid_awburst — AWBURST = 2'b11");

assert property (invalid_arburst)
  else $warning("ASSERTION FAILED: invalid_arburst — ARBURST = 2'b11");

assert property (last_w_beat)
  else $warning("ASSERTION FAILED: last_w_beat — WLAST without WVALID && WREADY");

assert property (last_r_beat)
  else $warning("ASSERTION FAILED: last_r_beat — RLAST without RVALID && RREADY");

assert property (valid_wstrb)
  else $warning("ASSERTION FAILED: valid_wstrb — WSTRB was all 0 on WVALID && WREADY");

assert property (valid_awlen)
  else $warning("ASSERTION FAILED: valid_awlen — AWLEN > 255");

assert property (valid_arlen)
  else $warning("ASSERTION FAILED: valid_arlen — ARLEN > 255");

assert property (stable_wvalid)
  else $warning("ASSERTION FAILED: stable_wvalid — WDATA changed while WVALID && !WREADY");

assert property (stable_awaddr)
  else $warning("ASSERTION FAILED: stable_awaddr — AWADDR changed while AWVALID && !AWREADY");

assert property (stable_araddr)
  else $warning("ASSERTION FAILED: stable_araddr — ARADDR changed while ARVALID && !ARREADY");

assert property (w_before_b)
  else $warning("ASSERTION FAILED: w_before_b — BVALID occurred before write_en");

assert property (ar_before_r)
  else $warning("ASSERTION FAILED: ar_before_r — RVALID occurred before read_en");


endmodule
