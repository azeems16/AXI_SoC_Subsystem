class rst_sync_coverage;
 
logic clk;
logic rst_async;
logic rst_sync;
  
covergroup cvr_rst @ (posedge clk);
    option.per_instance = 1;
    
    coverpoint rst_async { bins off = {0}; bins on = {1}; }
    coverpoint rst_sync  { bins off = {0}; bins on = {1}; }
  endgroup
  
  function new(input logic clk);
    this.clk = clk;
    cvr_rst = new();
  endfunction
  
  function void drive_sample(
    input logic rst_async	,
    input logic rst_sync
  );
    this.rst_async = rst_async;
    this.rst_sync  = rst_sync;
    
    cvr_rst.sample();
  endfunction
  
endclass