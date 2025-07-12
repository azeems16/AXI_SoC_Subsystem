`include "uvm_macros.svh"
 import uvm_pkg::*;
 
module axi4_uvm_tb;

axi4_intf #(32, 32) axi4_intf();

axi4_slave #(
    .ID_WIDTH   (4),
    .ADDR_WIDTH (32),
    .DATA_WIDTH (32),
    .BASE_ADDR  (32'h0)
) dut (
    .ACLK         (axi4_intf.ACLK),
    .ARESETN      (axi4_intf.ARESETN),

    // Write Address Channel
    .S_AXI_AWID    ('0), // Not included in your interface; tie off if unused
    .S_AXI_AWADDR  (axi4_intf.AWADDR),
    .S_AXI_AWLEN   (axi4_intf.AWLEN),
    .S_AXI_AWSIZE  (axi4_intf.AWSIZE),
    .S_AXI_AWBURST (axi4_intf.AWBURST),
    .S_AXI_AWVALID (axi4_intf.AWVALID),
    .S_AXI_AWREADY (axi4_intf.AWREADY),

    // Write Data Channel
    .S_AXI_WDATA   (axi4_intf.WDATA),
    .S_AXI_WSTRB   (axi4_intf.WSTRB),
    .S_AXI_WLAST   (axi4_intf.WLAST),
    .S_AXI_WVALID  (axi4_intf.WVALID),
    .S_AXI_WREADY  (axi4_intf.WREADY),

    // Write Response Channel
    .S_AXI_BID     (), // Not in interface, unused – leave unconnected or tie off
    .S_AXI_BRESP   (axi4_intf.BRESP),
    .S_AXI_BVALID  (axi4_intf.BVALID),
    .S_AXI_BREADY  (axi4_intf.BREADY),

    // Read Address Channel
    .S_AXI_ARID    ('0), // Not in interface; tie off or ignore
    .S_AXI_ARADDR  (axi4_intf.ARADDR),
    .S_AXI_ARLEN   (axi4_intf.ARLEN),
    .S_AXI_ARSIZE  (axi4_intf.ARSIZE),
    .S_AXI_ARBURST (axi4_intf.ARBURST),
    .S_AXI_ARVALID (axi4_intf.ARVALID),
    .S_AXI_ARREADY (axi4_intf.ARREADY),

    // Read Data Channel
    .S_AXI_RID     (), // Not in interface; leave unconnected
    .S_AXI_RDATA   (axi4_intf.RDATA),
    .S_AXI_RRESP   (axi4_intf.RRESP),
    .S_AXI_RLAST   (axi4_intf.RLAST),
    .S_AXI_RVALID  (axi4_intf.RVALID),
    .S_AXI_RREADY  (axi4_intf.RREADY),

    .write_en      (), // Optional: connect to signal or leave open
    .read_en       ()
);

initial begin
    axi4_intf.ACLK <= 0;
end

always #5 axi4_intf.ACLK = ~axi4_intf.ACLK;

initial begin
  axi4_intf.ARESETN = 0;
  #20;
  axi4_intf.ARESETN = 1;
end

initial begin
    uvm_config_db#(virtual axi4_intf)::set(null, "*", "axi4_intf", axi4_intf);
    run_test("axi4_test");
end

initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, axi4_uvm_tb);
end
endmodule