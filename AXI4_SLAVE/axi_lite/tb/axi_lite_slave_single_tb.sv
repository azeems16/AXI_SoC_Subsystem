// Following testbench is suited for a single read/write transaction

module axi_lite_slave_single_tb;

    // Clock and Reset
    logic        ACLK           ;
    logic        ARESETN        ;

    // Write Address Channel 
    logic [31:0] S_AXI_AWADDR   ;
    logic        S_AXI_AWVALID  ;
    wire         S_AXI_AWREADY  ;

    // Write Channel
    logic [31:0]  S_AXI_WDATA   ;
    logic [3:0]   S_AXI_WSTRB   ;
    logic         S_AXI_WVALID  ;
    wire          S_AXI_WREADY  ; 

    // Write Response Channel
    logic         S_AXI_BREADY  ; 
    wire  [1:0]   S_AXI_BRESP   ;
    wire          S_AXI_BVALID  ;

    // Read Address Channel
    logic [31:0]  S_AXI_ARADDR  ;
    logic         S_AXI_ARVALID ;
    wire          S_AXI_ARREADY ;

    // Read Channel
    logic         S_AXI_RREADY  ; 
    wire [31:0]   S_AXI_RDATA   ;
    wire  [1:0]   S_AXI_RRESP   ;
    wire          S_AXI_RVALID  ;

coverage_axi_lite cov_inst;

initial begin
    cov_inst = new();
end

always @ (posedge ACLK) begin
    if(ARESETN) begin
        cov_inst.drive_sample(
            ACLK,
            ARESETN,
            S_AXI_AWVALID,
            S_AXI_AWREADY,
            S_AXI_WSTRB,
            S_AXI_WVALID,
            S_AXI_WREADY,
            S_AXI_BREADY,
            S_AXI_BVALID,
            S_AXI_ARVALID,
            S_AXI_ARREADY,
            S_AXI_RREADY,
            S_AXI_RVALID
        );
    end
end

axi_lite_slave slave (
    .ACLK             (ACLK         )   ,
    .ARESETN          (ARESETN      )   ,
    .S_AXI_AWADDR     (S_AXI_AWADDR )   ,
    .S_AXI_AWVALID    (S_AXI_AWVALID)   ,
    .S_AXI_AWREADY    (S_AXI_AWREADY)   ,
    .S_AXI_WDATA      (S_AXI_WDATA  )   ,
    .S_AXI_WSTRB      (S_AXI_WSTRB  )   ,
    .S_AXI_WVALID     (S_AXI_WVALID )   ,
    .S_AXI_WREADY     (S_AXI_WREADY )   ,
    .S_AXI_BRESP      (S_AXI_BRESP  )   ,
    .S_AXI_BVALID     (S_AXI_BVALID )   ,
    .S_AXI_BREADY     (S_AXI_BREADY )   ,
    .S_AXI_ARADDR     (S_AXI_ARADDR )   ,
    .S_AXI_ARVALID    (S_AXI_ARVALID)   ,
    .S_AXI_ARREADY    (S_AXI_ARREADY)   , 
    .S_AXI_RDATA      (S_AXI_RDATA  )   ,
    .S_AXI_RRESP      (S_AXI_RRESP  )   ,
    .S_AXI_RVALID     (S_AXI_RVALID )   ,
    .S_AXI_RREADY     (S_AXI_RREADY )
);

// Clock Toggle
always #5 ACLK = ~ACLK;

// Clock/Reset Intialization
initial begin
    ACLK            = 1'b0;
    ARESETN         = 1'b0;
    #8;
    ARESETN         = 1'b1;
end

// Stimulus Intialization
initial begin
    // Write
    S_AXI_AWADDR    = 32'h0; 
    S_AXI_AWVALID   = 1'b0;
    S_AXI_WDATA     = 32'hDEADBEEF;
    S_AXI_WSTRB     = 4'hF;
    S_AXI_WVALID    = 1'h0;
    S_AXI_BREADY    = 1'h0;

    // Read
    S_AXI_ARADDR    = 32'h0;
    S_AXI_ARVALID   = 1'b0;
    S_AXI_RREADY    = 1'b0;
end

//Stimulus
initial begin
    @(posedge ARESETN); // exiting reset

    // Write + Read Stimulus
    // Asserting valid/ready signals 
    #5;
    S_AXI_AWADDR = 32'hC;
    S_AXI_ARADDR = 32'hC;
    S_AXI_WDATA     = 32'hDEADBEEF;
    #1;
    S_AXI_AWVALID = 1'b1;
    S_AXI_ARVALID = 1'b1;
    S_AXI_WVALID  = 1'b1;
    #5;
    S_AXI_BREADY  = 1'b1;
    S_AXI_RREADY  = 1'b1;

    $display("[AXI States]: SAXI_AWADDR: 0x%0h, S_AXI_ARADDR: 0x%0h, S_AXI_WDATA: 0x%0h", S_AXI_AWADDR, S_AXI_ARADDR, S_AXI_WDATA);

// Deasserts after handshake detection
fork    // This is needed for deasserts so we don't stall on one wait statement 
    begin
        wait (S_AXI_AWREADY);
        @(posedge ACLK);
        S_AXI_AWVALID = 1'b0;
        $display("Address Write Channel Handshake Detected, deasserting S_AXI_AWVALID");
    end

    begin
        wait(S_AXI_WREADY);
        @(posedge ACLK);
        S_AXI_WVALID  = 1'b0;
        $display("Write Channel Handshake Detected, deasserting S_AXI_WVALID");
    end

    begin
        wait(S_AXI_BVALID);
        @(posedge ACLK);
        S_AXI_BREADY  = 1'b0;
        $display("Response Write Channel Handshake Detected, deasserting S_AXI_BREADY");
    end

    begin
        wait(S_AXI_ARREADY);
        @(posedge ACLK);
        S_AXI_ARVALID = 1'b0;
        $display("Address Read Channel Handshake Detected, deasserting S_AXI_ARVALID");
    end

    begin
        wait(S_AXI_RVALID);
        @(posedge ACLK);
        S_AXI_RREADY  = 1'b0;
        $display("Read Channel Handshake Detected, deasserting S_AXI_RREADY");
    end
join

    #50;
    $display("Simulation Done");
    $finish;
end

initial begin
    $dumpfile("dump.vcd");
    $dumpvars(1, axi_lite_slave_single_tb); // or top module name
    $dumpvars(1, axi_lite_slave_single_tb.slave.regfile[3]); // or top module name
    $dumpvars(1, axi_lite_slave_single_tb.slave.regfile[2]); // or top module name
    $dumpvars(1, axi_lite_slave_single_tb.slave.regfile[1]); // or top module name
    $dumpvars(1, axi_lite_slave_single_tb.slave.regfile[0]); // or top module name
end


endmodule