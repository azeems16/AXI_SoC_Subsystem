`include "soc_timer_coverage.sv"
module soc_timer_tb;
import soc_timer_reg_pkg::*;

parameter ADDR_WIDTH = 5;
parameter DATA_WIDTH = 32;

logic                      ACLK    ;
logic                      ARESETN ;
logic [ADDR_WIDTH-1:0]     AWADDR  ;
logic                      AWVALID ;
logic                      AWREADY ;
logic [DATA_WIDTH-1:0]     WDATA   ;
logic [(DATA_WIDTH/8)-1:0] WSTRB   ;
logic                      WVALID  ;
logic                      WREADY  ;
logic [1:0]                BRESP   ;
logic                      BVALID  ;
logic                      BREADY  ;
logic [ADDR_WIDTH-1:0]     ARADDR  ;
logic                      ARVALID ;
logic                      ARREADY ;
logic [DATA_WIDTH-1:0]     RDATA   ;
logic [1:0]                RRESP   ;
logic                      RVALID  ;
logic                      RREADY  ;
logic                      irq     ;

soc_timer timer (
    .ACLK    (ACLK)    ,
    .ARESETN (ARESETN) ,
    .AWADDR  (AWADDR ) ,
    .AWVALID (AWVALID) ,
    .AWREADY (AWREADY) ,
    .WDATA   (WDATA)   ,
    .WSTRB   (WSTRB)   ,
    .WVALID  (WVALID)  ,
    .WREADY  (WREADY)  ,
    .BRESP   (BRESP)   ,
    .BVALID  (BVALID)  ,
    .BREADY  (BREADY)  ,
    .ARADDR  (ARADDR)  ,
    .ARVALID (ARVALID) ,
    .ARREADY (ARREADY) ,
    .RDATA   (RDATA)   ,
    .RRESP   (RRESP)   ,
    .RVALID  (RVALID)  ,
    .RREADY  (RREADY)  ,
    .irq     (irq)     
);

soc_timer_coverage soc_timer_cvrg;

always @ (posedge ACLK) begin
    if (AWVALID && AWREADY) begin
        if (AWADDR == 32'h04) soc_timer_cvrg.cvrg_control_reg <= WDATA;
        if (AWADDR == 32'h10) soc_timer_cvrg.cvrg_clear_reg   <= WDATA;
    end
    if (ARVALID && ARREADY && ARADDR == 32'h0C)
        soc_timer_cvrg.cvrg_irq_reg <= RDATA;
end

initial soc_timer_cvrg = new(ACLK);

always @ (posedge ACLK) begin
    if (ARESETN) begin
        soc_timer_cvrg.drive_sample(ARESETN, AWVALID, AWREADY, AWADDR, WVALID, WREADY, WDATA, ARVALID, ARREADY, ARADDR, RVALID, RREADY, RDATA, irq);
    end
end

task automatic write(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] data);
    begin
        AWADDR = addr;
        WDATA  = data;
        WSTRB  = '1;

        #1;
        AWVALID = 1'b1;
        WVALID  = 1'b1;
        #5;
        BREADY  = 1'b1;
        
        fork    // This is needed for deasserts so we don't stall on one wait statement 
            begin
                wait (AWREADY);
                @(posedge ACLK);
                #1 AWVALID = 1'b0;
                // $display("Address Write Channel Handshake Detected, deasserting S_AXI_AWVALID");
            end

            begin
                wait(WREADY);
                @(posedge ACLK);
                #1 WVALID  = 1'b0;
                // $display("Write Channel Handshake Detected, deasserting S_AXI_WVALID");
            end

            begin
                wait(BVALID);
                @(posedge ACLK);
                #1 BREADY  = 1'b0;
                // $display("Response Write Channel Handshake Detected, deasserting S_AXI_BREADY");
            end
        join

        // $display("Write complete @ t = %0d. Wrote data = 0x%0h at address = 0x%0h", $realtime(), WDATA, AWADDR);
    end
endtask

task automatic read(input logic [ADDR_WIDTH-1:0] addr);
    
    begin
        ARADDR = addr;
        #1;
        ARVALID = 1'b1;
        #5;
        RREADY  = 1'b1;

        fork
            begin
                wait(ARREADY);
                @(posedge ACLK);
                #1 ARVALID = 1'b0;
            end

            begin
                wait(RVALID);
                @(posedge ACLK);
                #1 RREADY  = 1'b0;
            end
        join
        
        case(ARADDR)
            CONTROL_REG_OFFSET:    $display("CONTROL REGISTER CONFIG (0x04) is: %0b", RDATA);
            COUNTER_REG_OFFSET:    $display("COUNTER VALUE IS: %0d", RDATA);
            INT_STATUS_REG_OFFSET: $display("INTERRUPT HAS TRIGGERED: %0b", RDATA);
        endcase
    end
endtask

always #5 ACLK = ~ACLK;

// Initialization
initial begin
    ACLK    =  0;
    ARESETN =  0;

    AWADDR  = '0;
    AWVALID = '0;

    WDATA   = '0;
    WVALID  = '0;

    BREADY  = '0;

    ARADDR  = '0;
    ARVALID = '0;

    RREADY  = '0;
end

//Stimulus
initial begin
    repeat(2) @(posedge ACLK);
    ARESETN = 1;

    // 1) Load 10, No IRQ Mask, No Auto Reload, Start Timer
    write(LOAD_REG_OFFSET, 32'd10); 
    write(CONTROL_REG_OFFSET, 32'b001);
    
    #10;
    read(COUNTER_REG_OFFSET);
    read(CONTROL_REG_OFFSET);
    $display("Writing to LOAD_REG_OFFSET (00) and CONTROL_REG_OFFSET(04)");
    
    #500;
    read(INT_STATUS_REG_OFFSET);
    
    write(CONTROL_REG_OFFSET, 32'b000);
    write(INT_CLEAR_REG_OFFSET, 32'd1);
    
    $display("Writing to CONTROL_REG_OFFSET (04) and INT_CLEAR_REG_OFFSET(10)");

    read(CONTROL_REG_OFFSET);
    read(COUNTER_REG_OFFSET);
    read(INT_STATUS_REG_OFFSET);
    
    #20;
    write(INT_CLEAR_REG_OFFSET, 32'd0);
    
    $display("Writing to INT_CLEAR_REG_OFFSET (10)");
    
    read(CONTROL_REG_OFFSET);
    read(COUNTER_REG_OFFSET);
    read(INT_STATUS_REG_OFFSET);

    // // 2) Load 5, No IRQ Mask, No Auto Reload, Start Timer
    write(LOAD_REG_OFFSET, 32'd5);
    write(CONTROL_REG_OFFSET, 32'b011);
    
    $display("Writing to LOAD_REG_OFFSET (00) and CONTROL_REG_OFFSET(04)");
    
    read(CONTROL_REG_OFFSET);
    repeat(10) #1.4 read(COUNTER_REG_OFFSET);
    read(INT_STATUS_REG_OFFSET);
    
    #200;
  write(CONTROL_REG_OFFSET, 32'b000);
    write(INT_CLEAR_REG_OFFSET, 32'd1);
    
    $display("Writing to CONTROL_REG_OFFSET (04) and INT_CLEAR_REG_OFFSET(10)");
    
    read(CONTROL_REG_OFFSET);
    read(COUNTER_REG_OFFSET);
    read(INT_STATUS_REG_OFFSET);
    #20;
    
    write(INT_CLEAR_REG_OFFSET, 32'd0);

    $display("Writing to INT_CLEAR_REG_OFFSET(10)");

    read(CONTROL_REG_OFFSET);
    read(COUNTER_REG_OFFSET);
    read(INT_STATUS_REG_OFFSET);
    
    // 3) Load 3, IRQ Mask, No Auto Reload, Start Timer
    write(LOAD_REG_OFFSET, 32'd3);
    write(CONTROL_REG_OFFSET, 32'b101);

    $display("Writing to LOAD_REG_OFFSET(00) and CONTROL_REG_OFFSET(04)");

    read(CONTROL_REG_OFFSET);
  	read(COUNTER_REG_OFFSET);
    read(INT_STATUS_REG_OFFSET);
    #100;
    write(CONTROL_REG_OFFSET, 32'b000);

    $display("Writing to CONTROL_REG_OFFSET(04)");

    read(CONTROL_REG_OFFSET);
    read(COUNTER_REG_OFFSET);
    read(INT_STATUS_REG_OFFSET);
    // 4) Get Counter + Status
    write(INT_CLEAR_REG_OFFSET, 32'd1);

    $display("Writing to INT_CLEAR_REG_OFFSET(10)");

    read(INT_STATUS_REG_OFFSET);
    read(COUNTER_REG_OFFSET);

    #100 $finish;
end

// Waveforms
initial begin
    $dumpfile("soc_timer_tb.vcd");     // VCD output file name
    $dumpvars(0, soc_timer_tb);        // Dump all variables recursively from testbench top
end


endmodule