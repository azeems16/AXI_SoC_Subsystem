module cdc_2flop_sync #(
  parameter int DATA_WIDTH = 4
) (
  input  logic clk,
  input  logic rst_n,
  input  logic [DATA_WIDTH-1:0] d_async,
  output logic [DATA_WIDTH-1:0] d_sync
);

logic [DATA_WIDTH-1:0] q_ff1, q_ff2;

always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        q_ff1 <= '0;
        q_ff2 <= '0;
    end
    else begin
        q_ff1 <= d_async;
        q_ff2 <= q_ff1;
    end
end

assign d_sync = q_ff2;

endmodule