// Following testbench is suited for a single read/write transaction

module axi_lite_slave_multi_tb;

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

// Write + Read + initialize Tasks

task automatic initialize();
    begin
        S_AXI_AWADDR    = 32'h0 ;
        S_AXI_AWVALID   = 1'b0  ;
        S_AXI_WDATA     = 32'h0 ;
        S_AXI_WSTRB     = 4'hF  ;
        S_AXI_WVALID    = 1'h0  ;
        S_AXI_BREADY    = 1'h0  ;

        // Read
        S_AXI_ARADDR    = 32'h0 ;
        S_AXI_ARVALID   = 1'b0  ;
        S_AXI_RREADY    = 1'b0  ;

        $display("Testbench has been initialized");
    end
endtask

task automatic write(input logic [31:0] addr, input logic[31:0] data);
    begin
        S_AXI_AWADDR = addr;
        S_AXI_WDATA  = data;

        #1;
        S_AXI_AWVALID = 1'b1;
        S_AXI_WVALID  = 1'b1;
        #5;
        S_AXI_BREADY  = 1'b1;

        $display("[t= %0d]: Writing data = 0x%0h to S_AXI_AWADDR: 0x%0h", $realtime(), S_AXI_WDATA, S_AXI_AWADDR);

        fork    // This is needed for deasserts so we don't stall on one wait statement 
            begin
                wait (S_AXI_AWREADY);
                @(posedge ACLK);
                #1 S_AXI_AWVALID = 1'b0;
                $display("Address Write Channel Handshake Detected, deasserting S_AXI_AWVALID");
            end

            begin
                wait(S_AXI_WREADY);
                @(posedge ACLK);
                #1 S_AXI_WVALID  = 1'b0;
                $display("Write Channel Handshake Detected, deasserting S_AXI_WVALID");
            end

            begin
                wait(S_AXI_BVALID);
                @(posedge ACLK);
                #1 S_AXI_BREADY  = 1'b0;
                $display("Response Write Channel Handshake Detected, deasserting S_AXI_BREADY");
            end
        join

        $display("Write complete @ t = %0d. Wrote data = 0x%0h at address = 0x%0h", $realtime(), S_AXI_WDATA, S_AXI_AWADDR);
    end
endtask

task automatic read(input logic [31:0] addr);
        begin
        S_AXI_ARADDR = addr;
        #1;
        S_AXI_ARVALID = 1'b1;
        #5;
        S_AXI_RREADY  = 1'b1;

        $display("[t= %0d]: Reading from S_AXI_ARADDR: 0x%0h", $realtime(), S_AXI_ARADDR);

        fork
            begin
                wait(S_AXI_ARREADY);
                @(posedge ACLK);
                #1 S_AXI_ARVALID = 1'b0;
                $display("Address Read Channel Handshake Detected, deasserting S_AXI_ARVALID");
            end

            begin
                wait(S_AXI_RVALID);
                @(posedge ACLK);
                #1 S_AXI_RREADY  = 1'b0;
                $display("Read Channel Handshake Detected, deasserting S_AXI_RREADY");
            end
        join

        $display("Read Complete @ t = %0d. Read from address = 0x%0h and received data = %0x0h", $realtime(), S_AXI_ARADDR, S_AXI_RDATA);
    end
endtask

// Clock Toggle
always #5 ACLK = ~ACLK;

// Clock/Reset Intialization
initial begin
    ACLK            = 1'b0;
    ARESETN         = 1'b0;
    #10;
    ARESETN         = 1'b1;
end

//Stimulus
initial begin
    initialize();
    @(posedge ARESETN); // exiting reset

    #10;
    $display("Starting directed AXI-Lite test sequence...");

    for (int i = 0; i < 4; i++) begin
        logic [31:0] addr, data;
        addr = 32'h0000_0004 * i;
        data = 32'h1000_0000 + i;

        // Write phase
        $display("\n[TXN %0d] WRITE 0x%0h to 0x%0h", i, data, addr);
        write(addr, data);

        #10;

        // Read phase
        $display("[TXN %0d] READ from 0x%0h", i, addr);
        read(addr);

        #20; // Space for clean waveform visibility
    end

    $display("\nAll directed AXI-Lite transactions complete.");

    #50;
    $display("Simulation Done");
    $finish;
end

initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, axi_lite_slave_multi_tb); // or top module name
    $dumpvars(0, axi_lite_slave_multi_tb.slave.regfile[3]); // or top module name
    $dumpvars(0, axi_lite_slave_multi_tb.slave.regfile[2]); // or top module name
    $dumpvars(0, axi_lite_slave_multi_tb.slave.regfile[1]); // or top module name
    $dumpvars(0, axi_lite_slave_multi_tb.slave.regfile[0]); // or top module name
end


endmodule