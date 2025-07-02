`include "cdc_harness_coverage.sv"
`include "cdc_harness_sva.sv"
module cdc_harness_tb;

parameter int DATA_WIDTH = 8;

logic                  wr_clk         ;
logic                  wr_rst_n_async ;
logic [DATA_WIDTH-1:0] wr_data        ;
logic                  wr_en          ;
logic                  wr_full        ;
logic                  rd_clk         ;
logic                  rd_rst_n_async ;
logic [DATA_WIDTH-1:0] rd_data        ;
logic                  rd_en          ;
logic                  rd_empty       ;

cdc_harness cdc_harness(
    .wr_clk          (wr_clk)           ,
    .wr_rst_n_async  (wr_rst_n_async)   ,
    .wr_data         (wr_data)          ,
    .wr_en           (wr_en)            ,
    .wr_full         (wr_full)          ,
    .rd_clk          (rd_clk)           ,
    .rd_rst_n_async  (rd_rst_n_async)   ,
    .rd_data         (rd_data)          ,
    .rd_en           (rd_en)            ,
    .rd_empty        (rd_empty)
);
  
cdc_harness_coverage cvrg_tb;
  
initial cvrg_tb = new(wr_clk, rd_clk);
  
always @ (posedge wr_clk) begin
  cvrg_tb.drive_sample_wr(wr_en, wr_full);      
end
  
    
always @ (posedge rd_clk) begin
  cvrg_tb.drive_sample_rd(rd_en, rd_empty);      
end

cdc_fifo_sva #(
  .DATA_WIDTH(DATA_WIDTH),
  .DEPTH(16)
) fifo_sva (
  .wr_clk(wr_clk),
  .wr_en(wr_en),
  .wr_full(wr_full),
  .rd_clk(rd_clk),
  .rd_en(rd_en),
  .rd_empty(rd_empty),
  .wr_rst_n_async(wr_rst_n_async),
  .rd_rst_n_async(rd_rst_n_async)
);
  
task automatic initialize();
    wr_en   = '0;
    wr_data = '0;
    rd_en   = '0;
endtask

// Clocks
initial wr_clk = 0;
initial rd_clk = 0;
always #10 wr_clk = ~wr_clk;
always #16 rd_clk = ~rd_clk;

// Reset
initial begin
    wr_rst_n_async = 1'b0;
    rd_rst_n_async = 1'b0;
    #50;
    wr_rst_n_async = 1'b1;
  	rd_rst_n_async = 1'b1;
end

// Stimulus
initial begin
    initialize();
    
    // Write with check for full

    @(posedge wr_rst_n_async);
    $display("START TRANSACTION 1: Normal Write");
  	repeat(2) @(posedge wr_clk);
    for(int i = 0; i < 16; i++) begin
        @(posedge wr_clk);
        if(!wr_full) begin
            wr_data = $urandom();
            wr_en   = 1'b1;
            $display("TRANSACTION 1: Write #%0d, wr_data = %0x0h", i, wr_data);
        end
        else begin
            $display("Transaction 1: Write #%0d, skipped FIFO full", i);
        end
    end
    @(posedge wr_clk);
    wr_en   = 1'b0;
    $display("END TRANSACTION 1: Normal Write");
	
  	#500;
//     Read with check for empty
    $display("START TRANSACTION 2: Normal Read");
    for(int i = 0; i < 16; i++) begin
        @(posedge rd_clk);
        if(!rd_empty) begin
            rd_en   = 1'b1;
            $display("TRANSACTION 2: Read #%0d, rd_data = %0x0h", i, rd_data);
        end
        else begin
            rd_en = 1'b0;
            $display("Transaction 2: Read #%0d, skipped FIFO empty", i);
        end
    end
    @(posedge rd_clk);
    rd_en   = 1'b0;
    $display("END TRANSACTION 2: Normal Read");

    #500;
    initialize();
    
    // Write without checking for full

    $display("START TRANSACTION 3: Writing without checking full flag");
    for(int i = 0; i < 18; i++) begin
        @(posedge wr_clk);
        wr_data = $urandom();
        wr_en   = 1'b1;
    $display("TRANSACTION 3, Write #%0d, wr_data = %0x0h", i, wr_data);
    end
    @(posedge wr_clk);
    wr_en   = 1'b0;
    $display("END TRANSACTION 3: Writing without checking full flag");

    // Read without checking for empty
    $display("START TRANSACTION 4: Reading without checking empty flag");
    for(int i = 0; i < 18; i++) begin
        @(posedge rd_clk);
        rd_en   = 1'b1;
        $display("TRANSACTION 4, Read #%0d, rd_data = %0x0h", i, rd_data);
    end
    @(posedge rd_clk);
    rd_en   = 1'b0;
    $display("END TRANSACTION 4: Reading without checking empty flag");

  $finish;
end

// Dump
initial begin
  $dumpfile("dump.vcd");
  $dumpvars(0, cdc_harness_tb);
  $dumpvars(1, cdc_harness.async_fifo);
end

endmodule