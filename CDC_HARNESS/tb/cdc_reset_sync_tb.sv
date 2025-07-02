`include "coverage.sv"

module cdc_reset_sync_tb;
    logic dst_clk       ;
    logic rst_n_async   ;  
    logic rst_n_sync    ;   

cdc_reset_sync #(
    .SYNC_DEPTH(3)
)
reset_sync (
    .dst_clk     (dst_clk    )  ,
    .rst_n_async (rst_n_async)  ,  
    .rst_n_sync  (rst_n_sync )
);
  
rst_sync_coverage cvrg_rst_tb;
  
initial begin
  cvrg_rst_tb = new(dst_clk);
end

  always @ (posedge dst_clk) begin
    cvrg_rst_tb.drive_sample(rst_n_async, rst_n_sync);
  end
always #5 dst_clk = ~dst_clk;

initial begin
    dst_clk     = 1'b0;

    rst_n_async = 1'b0;

    #25;

    rst_n_async = 1'b1;

    #100;

    $finish;

end

initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, cdc_reset_sync_tb); // or top module name
end


endmodule