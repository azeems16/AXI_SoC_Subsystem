typedef enum logic [0:0] {
    DMA_READ  = 1'b0,
    DMA_WRITE = 1'b1
} dma_op;

class dma_transaction;
// Fields
  rand bit [31:0] addr ;    // Transaction will have address 
  rand bit [31:0] data ;    // Object will have data
  rand bit dma_op op   ;    // Operand : READ/WRITE

  logic [1:0] bresp, rresp; // Outputs: rresp, bbresp

// Constructor
function new(string name = "transaction");
endfunction

endclass

class dma_driver;

// Intf + Mailbox (always instantiate)
virtual dma_slave_if.drv   vif;
mailbox #(dma_transaction) mbx;

// Constructor
function new(virtual dma_if.drv vif, mailbox #(dma_transaction) mbx);
    this.vif = vif;
    this.mbx = mbx;
endfunction

// Stimulus
task automatic reset();
    vif.AWVALID <= 0;
    vif.WVALID  <= 0;
    vif.BREADY  <= 0;
    vif.ARVALID <= 0;
    vif.RREADY  <= 0;

    vif.AWADDR  <= '0;
    vif.WDATA   <= '0;
    vif.ARADDR  <= '0;
endtask


task run();
    dma_transaction tr; // Create object
    forever begin
        mbx.get(tr); // get transaction object from mailbox

        @(posedge vif.ARESETN);
        @(posedge vif.ACLK);
        @(posedge vif.ACLK);
        reset();
        @(posedge vif.ACLK);
        @(posedge vif.ACLK);

        // Testbench-Like Testing, apply transaction object fields to intf
        if (tr.op == DMA_WRITE) begin
            fork 
                begin: AW_CHANNEL
                    // Write Address Channel
                    vif.AWADDR  <= tr.addr;
                    @(posedge vif.ACLK);
                    vif.AWVALID <= 1;
                    wait(vif.AWREADY && vif.AWVALID);
                    @(posedge vif.ACLK);
                    vif.AWVALID <= 0;
                end

                begin: W_CHANNEL
                    // Write Data Channel
                    vif.WDATA  <= tr.data;
                    @(posedge vif.ACLK);
                    vif.WVALID <= 1;
                    wait(vif.WREADY && vif.WVALID);
                    @(posedge vif.ACLK);
                    vif.WVALID <= 0;
                end
            join

            //B-Response Channel
            @(posedge vif.ACLK);
            vif.BREADY <= 1;
            wait(vif.BVALID && vif.BREADY);
            @(posedge vif.ACLK);
            tr.bresp  <= vif.BRESP;
            vif.BREADY <= 0;
        end
        else if (tr.op == DMA_READ) begin
            // Address Read Channel
            vif.ARADDR  <= tr.addr;
            @(posedge vif.ACLK);
            vif.ARVALID <= 1;
            wait(vif.ARVALID && vif.ARREADY);
            @(posedge vif.ACLK);
            vif.ARVALID <= 0;

            // Read Channel
            @(posedge vif.ACLK);
            vif.RREADY <= 1;
            wait(vif.RREADY && vif.RVALID);
            tr.data    <= vif.RDATA;
            @(posedge vif.ACLK);
            tr.rresp   <= vif.RRESP;
            vif.RREADY <= 0;
        end
    end
endtask

class dma_monitor;

  // Virtual interface with modport mon
  virtual dma_slave_if.mon vif;

  // Output mailbox to scoreboard / logger
  mailbox #(dma_transaction) mon_mbx;

  // Constructor
  function new(virtual dma_slave_if.mon vif,
               mailbox #(dma_transaction) mon_mbx);
    this.vif     = vif;
    this.mon_mbx = mon_mbx;
  endfunction

  // Main run task
  task run();
    forever begin

      // ================================
      // 1. WATCH FOR WRITE TRANSACTION
      // ================================
      if (vif.AWVALID && vif.AWREADY) begin
        dma_transaction tr = new();
        tr.op = DMA_WRITE;

        // Capture address
        @(posedge vif.ACLK);
        tr.addr = vif.AWADDR;

        // Wait for data
        wait(vif.WVALID && vif.WREADY);
        @(posedge vif.ACLK);
        tr.data = vif.WDATA;

        // Wait for response
        wait(vif.BVALID && vif.BREADY);
        @(posedge vif.ACLK);
        tr.bresp = vif.BRESP;

        // Send it out
        mon_mbx.put(tr);
      end

      // ================================
      // 2. WATCH FOR READ TRANSACTION
      // ================================
      else if (vif.ARVALID && vif.ARREADY) begin
        dma_transaction tr = new();
        tr.op = DMA_READ;

        // Capture address
        @(posedge vif.ACLK);
        tr.addr = vif.ARADDR;

        // Wait for read data
        wait(vif.RVALID && vif.RREADY);
        @(posedge vif.ACLK);
        tr.data  = vif.RDATA;
        tr.rresp = vif.RRESP;

        // Send it out
        mon_mbx.put(tr);
      end

      // ================================
      // 3. Default clock sync
      // ================================
      @(posedge vif.ACLK); // idle clock step if nothing happened
    end
  endtask

endclass

class dma_test;

  mailbox #(dma_transaction) drv_mbx;

  function new(mailbox #(dma_transaction) drv_mbx);
    this.drv_mbx = drv_mbx;
  endfunction

  // Test Class is like sequencer, it creates object and puts it in mailbox for driver to take out
  task run();
    dma_transaction tr;

    tr = new();
    tr.addr = 32'h10;
    tr.data = 32'hDEADBEEF;
    tr.op   = DMA_WRITE;
    drv_mbx.put(tr);

    tr = new();
    tr.addr = 32'h10;
    tr.op   = DMA_READ;
    drv_mbx.put(tr);
  endtask

endclass

class dma_scoreboard;

  mailbox #(dma_transaction) mon_mbx;
  bit [31:0] expected_data_map [bit[31:0]];

  function new(mailbox #(dma_transaction) mon_mbx);
    this.mon_mbx = mon_mbx;
  endfunction

  task run();
    dma_transaction tr;
    forever begin
      mon_mbx.get(tr);

      if (tr.op == DMA_WRITE) begin
        expected_data_map[tr.addr] = tr.data;
      end
      else if (tr.op == DMA_READ) begin
        bit [31:0] expected;
        expected = expected_data_map.exists(tr.addr) ? expected_data_map[tr.addr] : 'x;

        if (tr.data !== expected) begin
          $error("SCOREBOARD MISMATCH: Read 0x%08X from 0x%08X, expected 0x%08X",
                  tr.data, tr.addr, expected);
        end else begin
          $display("SCOREBOARD PASS: Read 0x%08X from 0x%08X", tr.data, tr.addr);
        end
      end
    end
  endtask

endclass
