`include "axi4_slave_coverage.sv"
module axi4_slave_tb;

  // Parameters
  parameter int          NUM_REGS   = 4;
  parameter integer      ID_WIDTH   = 4;
  parameter integer      ADDR_WIDTH = 32;
  parameter integer      DATA_WIDTH = 32;

  // DUT Port Wires
  logic ACLK;
  logic ARESETN;

  // Write Address Channel
  logic [ID_WIDTH-1:0]  S_AXI_AWID;
  logic [ADDR_WIDTH-1:0] S_AXI_AWADDR;
  logic [7:0]            S_AXI_AWLEN;
  logic [2:0]            S_AXI_AWSIZE;
  logic [1:0]            S_AXI_AWBURST;
  logic                  S_AXI_AWVALID;
  logic                  S_AXI_AWREADY;

  // Write Data Channel
  logic [DATA_WIDTH-1:0] S_AXI_WDATA;
  logic [(DATA_WIDTH/8)-1:0] S_AXI_WSTRB;
  logic                  S_AXI_WLAST;
  logic                  S_AXI_WVALID;
  logic                  S_AXI_WREADY;

  // Write Response Channel
  logic [ID_WIDTH-1:0]   S_AXI_BID;
  logic [1:0]            S_AXI_BRESP;
  logic                  S_AXI_BVALID;
  logic                  S_AXI_BREADY;

  // Read Address Channel
  logic [ID_WIDTH-1:0]   S_AXI_ARID;
  logic [ADDR_WIDTH-1:0] S_AXI_ARADDR;
  logic [7:0]            S_AXI_ARLEN;
  logic [2:0]            S_AXI_ARSIZE;
  logic [1:0]            S_AXI_ARBURST;
  logic                  S_AXI_ARVALID;
  logic                  S_AXI_ARREADY;

  // Read Data Channel
  logic [ID_WIDTH-1:0]   S_AXI_RID;
  logic [DATA_WIDTH-1:0] S_AXI_RDATA;
  logic [1:0]            S_AXI_RRESP;
  logic                  S_AXI_RLAST;
  logic                  S_AXI_RVALID;
  logic                  S_AXI_RREADY;

  // DUT Instantiation
  axi4_slave slave (
    .ACLK          (ACLK),
    .ARESETN       (ARESETN),

    // Write Address Channel
    .S_AXI_AWID    (S_AXI_AWID),
    .S_AXI_AWADDR  (S_AXI_AWADDR),
    .S_AXI_AWLEN   (S_AXI_AWLEN),
    .S_AXI_AWSIZE  (S_AXI_AWSIZE),
    .S_AXI_AWBURST (S_AXI_AWBURST),
    .S_AXI_AWVALID (S_AXI_AWVALID),
    .S_AXI_AWREADY (S_AXI_AWREADY),

    // Write Data Channel
    .S_AXI_WDATA   (S_AXI_WDATA),
    .S_AXI_WSTRB   (S_AXI_WSTRB),
    .S_AXI_WLAST   (S_AXI_WLAST),
    .S_AXI_WVALID  (S_AXI_WVALID),
    .S_AXI_WREADY  (S_AXI_WREADY),

    // Write Response Channel
    .S_AXI_BID     (S_AXI_BID),
    .S_AXI_BRESP   (S_AXI_BRESP),
    .S_AXI_BVALID  (S_AXI_BVALID),
    .S_AXI_BREADY  (S_AXI_BREADY),

    // Read Address Channel
    .S_AXI_ARID    (S_AXI_ARID),
    .S_AXI_ARADDR  (S_AXI_ARADDR),
    .S_AXI_ARLEN   (S_AXI_ARLEN),
    .S_AXI_ARSIZE  (S_AXI_ARSIZE),
    .S_AXI_ARBURST (S_AXI_ARBURST),
    .S_AXI_ARVALID (S_AXI_ARVALID),
    .S_AXI_ARREADY (S_AXI_ARREADY),

    // Read Data Channel
    .S_AXI_RID     (S_AXI_RID),
    .S_AXI_RDATA   (S_AXI_RDATA),
    .S_AXI_RRESP   (S_AXI_RRESP),
    .S_AXI_RLAST   (S_AXI_RLAST),
    .S_AXI_RVALID  (S_AXI_RVALID),
    .S_AXI_RREADY  (S_AXI_RREADY)
  );
  
axi4_slave_coverage axi4_slave_cg_tb;
 
initial axi4_slave_cg_tb = new(ACLK);
  
always @ (posedge ACLK) begin
  if (ARESETN) begin
    axi4_slave_cg_tb.drive_sample(
      S_AXI_AWREADY ,
      S_AXI_AWVALID ,
      S_AXI_AWBURST ,
      S_AXI_WSTRB   ,
      S_AXI_WVALID  ,
      S_AXI_WREADY  ,
      S_AXI_WLAST   ,
      S_AXI_BRESP   ,
      S_AXI_BVALID  ,
      S_AXI_BREADY  ,
      S_AXI_ARVALID ,
      S_AXI_ARREADY ,
      S_AXI_ARBURST ,
      S_AXI_RRESP   ,
      S_AXI_RVALID  ,
      S_AXI_RREADY  ,
      S_AXI_RLAST   
    );
  end
end

task automatic initialize();
    S_AXI_AWID      = '0;
    S_AXI_AWADDR    = '0;
    S_AXI_ARLEN     = '0;
    S_AXI_AWSIZE    = '0;
    S_AXI_AWBURST   = '0;
    S_AXI_AWVALID   = '0;

    S_AXI_WDATA     = '0;
    S_AXI_WSTRB     = '0;
    S_AXI_WLAST     = '0;
    S_AXI_WVALID    = '0;

    S_AXI_BREADY    = '0;
    
    S_AXI_ARID      = '0;
    S_AXI_ARADDR    = '0;
    S_AXI_ARLEN     = '0;
    S_AXI_ARSIZE    = '0;
    S_AXI_ARBURST   = '0;
    S_AXI_ARVALID   = '0;

    S_AXI_RREADY    = '0;
endtask

task automatic read(
    input logic [3:0]  ar_id    , 
    input logic [31:0] ar_addr  ,   
    input logic [7:0]  ar_len   , 
    input logic [2:0]  ar_size  ,
    input logic [1:0]  ar_burst 
);
    S_AXI_ARID    = ar_id    ;
    S_AXI_ARADDR  = ar_addr  ;
    S_AXI_ARLEN   = ar_len   ;
    S_AXI_ARSIZE  = ar_size  ;
    S_AXI_ARBURST = ar_burst ;

    #5;
    S_AXI_ARVALID = 1'b1;
    S_AXI_RREADY  = 1'b1;

    fork
      begin
        wait(S_AXI_ARREADY);
        @(posedge ACLK);
        #1 S_AXI_ARVALID = 1'b0;
        $display("AR-Channel Handshake Detected, deasserting S_AXI_ARVALID");
      end

      begin
        for (int beat = 0; beat <= ar_len; beat++) begin
          wait(S_AXI_RVALID);
          @(posedge ACLK);
        end
          #1 S_AXI_RREADY = 1'b0;
      end
    join
endtask

task automatic write(
    input logic [3:0]  aw_id     ,
    input logic [31:0] aw_addr   ,
    input logic [7:0]  aw_len    ,
    input logic [2:0]  aw_size   ,
    input logic [1:0]  aw_burst  ,
    input logic [31:0] w_data[]  ,
    input logic [3:0]  w_strb
);

    S_AXI_AWID    = aw_id    ;
    S_AXI_AWADDR  = aw_addr  ;
    S_AXI_AWLEN   = aw_len   ;
    S_AXI_AWSIZE  = aw_size  ;
    S_AXI_AWBURST = aw_burst ;
    S_AXI_WSTRB   = w_strb   ;
    

    fork
      begin: AW_HANDSHAKE
          S_AXI_AWVALID = 1'b1;
          wait(S_AXI_AWREADY && S_AXI_AWVALID);
          $display("AW-Channel Handshake Complete... Deasserting AWVALID");
          @(posedge ACLK);
          #1 S_AXI_AWVALID = 1'b0;
      end

      begin: W_HANDSHAKE
          @(posedge ACLK);
          S_AXI_WVALID = 1'b1;
          wait(slave.wr_state == 2'b10);  // wait until we are actually in WR_DATA state to latch on to beats
          for(int i = 0; i < w_data.size(); i++) begin
            @(posedge ACLK);  // must only latch w_data at rising edge of clock to align WDATA to CLK frequency
            S_AXI_WDATA = w_data[i];
            wait(S_AXI_WVALID && S_AXI_WREADY);
            if (i == w_data.size()-1) begin
              S_AXI_WLAST = 1'b1;
              @(posedge ACLK);
            end
          end
      
          S_AXI_WLAST = 0;
          S_AXI_WVALID = 0;
          $display("W-Channel Handshake Complete... Deasserting WVALID");
      end


      begin: B_HANDSHAKE
        #5;
        S_AXI_BREADY  = 1'b1;
        wait(S_AXI_BVALID && S_AXI_BREADY);
        $display("B-Channel Handshake Complete... Deasserting BREADY");
        @(posedge ACLK);
        #1 S_AXI_BREADY = 1'b0;
      end
    join
endtask

always #5 ACLK = ~ACLK;

// Initialize clock, reset, DUT inputs
initial begin
  ACLK    <= 1'b0;
  ARESETN <= 1'b0;
  initialize();
  #50;
  ARESETN <= 1'b1;
end

// Stimulus

initial begin
    logic [31:0] addr_out_of_range;
    logic [31:0] wdata[1];
    logic [1:0] burst_err;
    logic [31:0] addr;
    logic [3:0] wstrb_err;
  
  initialize();
  @(posedge ARESETN);
  // $display("Exiting Reset @ t = %0t", $realtime());

  // 1) Single Beat 
  $display("[START Single Beat Transaction: 5 WRITES, 5 READS] @ t= %0t", $realtime());
  for(int single_op = 0; single_op < 5; single_op++) begin
    logic [31:0] addr;
    logic [31:0] wdata[1];
    
    addr     = 32'h0000_0004 * single_op;
    wdata[0]    = $urandom();
    
    // Write phase
    $display("[TB] Writing TXN %0d:  WDATA= %d to WADDR= %0x0h, WLAST = %b, WVALID = %b, WREADY = %b", single_op, wdata[0], addr, S_AXI_WLAST, S_AXI_WVALID, S_AXI_WREADY);
    write(single_op, addr, 0, 3'b010, 2'b00, wdata, 4'b1111);

    #10;

    // Read phase
    read(single_op, addr, 0, 3'b010, 2'b00);
    $display("[TB] Reading TXN %0d:  RDATA= %d from RADDR= %0x0h, RLAST = %b, RVALID = %b, RREADY = %b", single_op, S_AXI_RDATA, addr, S_AXI_RLAST, S_AXI_RVALID, S_AXI_RREADY);

    #10;
  end
  $display("[ END  Single Beat Transaction: 5 WRITES, 5 READS] @ t= %0t", $realtime());
  
  initialize();
  #500;

  // 2) Multi Beat - FIXED Burst, Constant Data Size 
  $display("[START Multi Beat Fixed Burst Transaction: 3 WRITES, 3 READS] @ t= %0t", $realtime());
  for(int multi_op_fixed = 0; multi_op_fixed < 3; multi_op_fixed++) begin
    logic [31:0] addr;
    logic [31:0] wdata[8];

    addr = 32'h0000_0004 * multi_op_fixed;
    for(int i = 0; i <8; i++) begin
      wdata[i] = $urandom();
    end

    #100;
    // Write phase
    $display("[TB] Writing TXN %0d:  FIXED BURST to WADDR= %0x0h, WLAST = %b, WVALID = %b, WREADY = %b", multi_op_fixed, addr, S_AXI_WLAST, S_AXI_WVALID, S_AXI_WREADY);
    write(multi_op_fixed, addr, 7, 3'b010, 2'b00, wdata, 4'b1111);

    #10;

    // Read phase
    read(multi_op_fixed, addr, 7, 3'b010, 2'b00);
    $display("[TB] Reading TXN %0d:  RDATA= %0x0h from RADDR= %0x0h, RLAST = %b, RVALID = %b, RREADY = %b", multi_op_fixed, S_AXI_RDATA, addr, S_AXI_RLAST, S_AXI_RVALID, S_AXI_RREADY);

    #10;
  end
  $display("[ END Multi Beat Fixed Burst Transaction: 3 WRITES, 3 READS] @ t= %0t", $realtime());
  initialize();

  #500;

  // 3) Multi Beat - INCR Burst, Constant Data Size 
  $display("[START Multi Beat INCR Burst Transaction: 3 WRITES, 3 READS] @ t= %0t", $realtime());
  for(int multi_op_incr = 0; multi_op_incr < 3; multi_op_incr++) begin
    logic [31:0] addr;
    logic [31:0] wdata[8];

    addr = 32'h0000_0004 * multi_op_incr;
    for(int i = 0; i <8; i++) begin
      wdata[i] = i;
    end

    #100;
    // Write phase
    $display("[TB] Writing TXN %0d:  incr BURST to WADDR= %0x0h, WLAST = %b, WVALID = %b, WREADY = %b", multi_op_incr, addr, S_AXI_WLAST, S_AXI_WVALID, S_AXI_WREADY);

    write(multi_op_incr, addr, 7, 3'b010, 2'b01, wdata, 4'b1111);

    #10;

    // Read phase
    read(multi_op_incr, addr, 7, 3'b010, 2'b01);
    $display("[TB] Reading TXN %0d:  RDATA= %0x0h from RADDR= %0x0h, RLAST = %b, RVALID = %b, RREADY = %b", multi_op_incr, S_AXI_RDATA, addr, S_AXI_RLAST, S_AXI_RVALID, S_AXI_RREADY);

    #10;
  end
  initialize();

  #500;
  
  // 4) Multi Beat - WRAP Burst, Constant Data Size 
  $display("[START Multi Beat WRAP Burst Transaction: 3 WRITES, 3 READS] @ t= %0t", $realtime());
  for(int multi_op_wrap = 0; multi_op_wrap < 3; multi_op_wrap++) begin
    logic [31:0] addr;
    logic [31:0] wdata[8];

    addr = 32'h0000_0004 * multi_op_wrap;
    for(int i = 0; i <8; i++) begin
      wdata[i] = i;
    end

    #100;
    // Write phase
    $display("[TB] Writing TXN %0d:  WRAP BURST to WADDR= %0x0h, WLAST = %b, WVALID = %b, WREADY = %b", multi_op_wrap, addr, S_AXI_WLAST, S_AXI_WVALID, S_AXI_WREADY);

    write(multi_op_wrap, addr, 7, 3'b010, 2'b10, wdata, 4'b1111);

    #10;

    // Read phase
    read(multi_op_wrap, addr, 7, 3'b010, 2'b10);
    $display("[TB] Reading TXN %0d:  RDATA= %0x0h from RADDR= %0x0h, RLAST = %b, RVALID = %b, RREADY = %b", multi_op_wrap, S_AXI_RDATA, addr, S_AXI_RLAST, S_AXI_RVALID, S_AXI_RREADY);

    #10;
  end
  $display("[ END Multi Beat WRAP Burst Transaction: 3 WRITES, 3 READS] @ t= %0t", $realtime());
  
  initialize();

  // 5) Error Cases: misalignment, burst error, strobe error
  $display("[START ERROR TESTING @ t= %0t", $realtime());
    
    addr_out_of_range = 32'h0000_0011;
    wdata[0]          = $urandom();
    
    // Write phase
    $display("[TB] TESTING WRITE ADDRESS OUT OF RANGE");
    write(0, addr_out_of_range, 0, 3'b010, 2'b00, wdata, 4'b1111);

    #10;

    // Read phase
    read(0, addr_out_of_range, 0, 3'b010, 2'b00);
    $display("[TB] TESTING READ ADDRESS OUT OF RANGE");

    #10;
    initialize();

    burst_err = 2'b11;
    addr = 32'h0000_0000;
    
    $display("[TB] TESTING WRITE BURST ERROR");
    write(0, addr, 0, 3'b010, burst_err, wdata, 4'b1111);

    #10;

    // Read phase
    read(0, addr, 0, 3'b010, burst_err);
    $display("[TB] TESTING READ BURST ERROR");
    
    #10;
    initialize();

    wstrb_err = 4'b0000;
    
    $display("[TB] TESTING WRITE STROBE ERROR");
    write(0, addr, 0, 3'b010, 2'b00, wdata, wstrb_err);

    $display("[END ERROR TESTING @ t= %0t", $realtime());

  initialize();

  #50;
  $display("Simulation Done");
  $finish;
end

initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, axi4_slave_tb); // or top module name
    $dumpvars(0, axi4_slave_tb.slave.regfile[7]); // or top module name
    $dumpvars(0, axi4_slave_tb.slave.regfile[6]); // or top module name
    $dumpvars(0, axi4_slave_tb.slave.regfile[5]); // or top module name
    $dumpvars(0, axi4_slave_tb.slave.regfile[4]); // or top module name
    $dumpvars(0, axi4_slave_tb.slave.regfile[3]); // or top module name
    $dumpvars(0, axi4_slave_tb.slave.regfile[2]); // or top module name
    $dumpvars(0, axi4_slave_tb.slave.regfile[1]); // or top module name
    $dumpvars(0, axi4_slave_tb.slave.regfile[0]); // or top module name
    $dumpvars(0, axi4_slave_tb.slave.wr_state  ); // or top module name
end

endmodule