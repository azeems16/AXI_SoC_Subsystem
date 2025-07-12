class axi4_agent extends uvm_agent;
`uvm_component_utils(axi4_agent)

uvm_sequencer#(axi_txn#(32,32)) seqr;
axi_driver drv;
axi_monitor mon;
virtual axi4_intf vif;

function new(input string name = "agent", uvm_component parent = null);
    super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual axi4_intf)::get(this, "", "vif", vif))
        `uvm_fatal("AGENT", "No VIF found for axi_agent");

    // Pass VIF to driver and monitor
    uvm_config_db#(virtual axi4_intf)::set(this, "drv", "vif", vif);
    uvm_config_db#(virtual axi4_intf.monitor)::set(this, "mon", "vif", vif.monitor);

    drv  = axi4_driver::type_id::create("drv", this);
    mon  = axi4_monitor::type_id::create("mon", this);
    seqr = uvm_sequencer#(axi_txn#(32,32))::type_id::create("seqr", this);
endfunction

function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    drv.seq_item_port.connect(seqr.seq_item_export);
endfunction

endclass