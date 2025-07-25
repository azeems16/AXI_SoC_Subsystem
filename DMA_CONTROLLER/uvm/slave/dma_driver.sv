class dma_driver extends uvm_driver#(dma_txn#(32,32));
`uvm_component_utils(dma_driver)

virtual dma_slave_if.drv vif;
dma_txn#(32,32) tr;

function new(input string name = "drv", uvm_component parent = null);
    super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tr = dma_txn#(32,32)::type_id::create("tr");

    if(!uvm_config_db#(virtual dma_slave_if.drv)::get(this,"","vif",vif)) begin
    `uvm_error("DRV","Unable to access Interface");
    end
endfunction

task reset_dut();
    vif.ARESETN <= 0;
    repeat(2) @(posedge vif.ACLK);
    vif.ARESETN <= 1;
    
    repeat(5) begin

        vif.AWADDR  <= '0;
        vif.AWVALID <=  0;

        vif.WDATA   <= '0;
        vif.WSTRB   <= '1;
        vif.WVALID  <=  0;
        
        vif.BREADY  <=  0;

        vif.ARADDR  <= '0;
        vif.ARVALID <=  0;

        vif.RREADY  <=  0;

        `uvm_info("DRV", "System Reset : Start of Simulation", UVM_MEDIUM);
        @(posedge vif.ACLK);
    end
endtask

task drive_write(dma_txn#(32, 32) tr);
    fork
        begin
            @(posedge vif.ACLK);
            vif.AWADDR  <= tr.addr;
            vif.AWVALID <= 1;

            wait (vif.AWVALID && vif.AWREADY);
            @(posedge vif.ACLK);
            vif.AWVALID <= 0;
        end

        begin
            @(posedge vif.ACLK);
            vif.WDATA  <= tr.data;
            vif.WSTRB  <= tr.wstrb;
            vif.WVALID <= 1;

            wait(vif.WVALID && vif.WREADY);
            @(posedge vif.ACLK);
            vif.WVALID <= 0;
        end
    join

    @(posedge vif.ACLK);
    vif.BREADY <= 1;
    wait(vif.BVALID && vif.BREADY);
    tr.resp <= vif.BRESP;
    @(posedge vif.ACLK);
    vif.BREADY <= 0;        
endtask

task drive_read(dma_txn#(32, 32) tr);
    @(posedge vif.ACLK);
    vif.ARADDR  <= tr.addr;
    vif.ARVALID <= 1;
    wait(vif.ARREADY && vif.ARVALID);
    vif.ARVALID <= 0;
    vif.RREADY  <= 1;

    wait(vif.RREADY && vif.RVALID);
    tr.rdata <= vif.RDATA;
    tr.resp  <= vif.RRESP;

    @(posedge vif.ACLK);
    vif.RREADY <= 0;
endtask

virtual task run_phase(uvm_phase phase);
    reset_dut();
    forever begin
        seq_item_port.get_next_item(tr);
        if (tr.is_write) begin
            drive_write(tr);
        end
        else begin
            drive_read(tr);
        end
        seq_item_port.item_done(tr);
    end
endtask
endclass