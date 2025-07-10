class axi4_test extends uvm_test;
`uvm_component_utils(axi4_test)

axi4_env#(axi_txn#(32,32)) env;

// Sequences
single_beat_fixed_write#(axi_txn#(32,32)) single_beat_fixed_write ;
multil_beat_fixed_write#(axi_txn#(32,32)) multil_beat_fixed_write ;
multil_beat_incr_write#(axi_txn#(32,32))  multil_beat_incr_write  ;
multil_beat_wrap_write#(axi_txn#(32,32))  multil_beat_wrap_write  ;

single_beat_fixed_read#(axi_txn#(32,32)) single_beat_fixed_read   ;
multil_beat_fixed_read#(axi_txn#(32,32)) multil_beat_fixed_read   ;
multil_beat_incr_read#(axi_txn#(32,32))  multil_beat_incr_read    ;
multil_beat_wrap_read#(axi_txn#(32,32))  multil_beat_wrap_read    ;

invalid_wstrb#(axi_txn#(32,32))          invalid_wstrb   ; 
invalid_burst#(axi_txn#(32,32))          invalid_burst   ; 
misaligned_addr#(axi_txn#(32,32))        misaligned_addr ; 

function new(input string name = "axi4_test", uvm_component parent = null);
    super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    env = axi4_env#(axi_txn#(32,32))::type_id::create("env", this);

    single_beat_fixed_write = single_beat_fixed_write#(axi_txn#(32,32))::type_id::create("single_beat_fixed_write");
    multil_beat_fixed_write = multil_beat_fixed_write#(axi_txn#(32,32))::type_id::create("multil_beat_fixed_write");
    multil_beat_incr_write  = multil_beat_incr_write#(axi_txn#(32,32))::type_id::create("multil_beat_incr_write");
    multil_beat_wrap_write  = multil_beat_wrap_write#(axi_txn#(32,32))::type_id::create("multil_beat_wrap_write");
    single_beat_fixed_read  = single_beat_fixed_read#(axi_txn#(32,32))::type_id::create("single_beat_fixed_read");
    multil_beat_fixed_read  = multil_beat_fixed_read#(axi_txn#(32,32))::type_id::create("multil_beat_fixed_read");
    multil_beat_incr_read   = multil_beat_incr_read#(axi_txn#(32,32))::type_id::create("multil_beat_incr_read");
    multil_beat_wrap_read   = multil_beat_wrap_read#(axi_txn#(32,32))::type_id::create("multil_beat_wrap_read");
    invalid_wstrb           = invalid_wstrb#(axi_txn#(32,32))::type_id::create("invalid_wstrb");
    invalid_burst           = invalid_burst#(axi_txn#(32,32))::type_id::create("invalid_burst");
    misaligned_addr         = misaligned_addr#(axi_txn#(32,32))::type_id::create("misaligned_addr");
endfunction


virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    single_beat_fixed_write.start(env.agent.seqr);
    #10;
    single_beat_fixed_read.start(env.agent.seqr); 
    #50;
    
    multil_beat_fixed_write.start(env.agent.seqr);
    #10;
    multil_beat_fixed_read.start(env.agent.seqr); 
    #50;
    
    multil_beat_incr_write.start(env.agent.seqr); 
    #10;
    multil_beat_incr_read.start(env.agent.seqr);  
    #50;
    
    multil_beat_wrap_write.start(env.agent.seqr); 
    #10;
    multil_beat_wrap_read.start(env.agent.seqr);  
    #50;
    
    invalid_wstrb.start(env.agent.seqr);          
    #50;
    invalid_burst.start(env.agent.seqr);          
    #50;
    misaligned_addr.start(env.agent.seqr);
    #50;
    phase.drop_objection(this);
endtask

endclass