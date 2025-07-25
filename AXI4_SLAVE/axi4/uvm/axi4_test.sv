class axi4_test extends uvm_test;
`uvm_component_utils(axi4_test)

axi4_env env;

// Sequences
single_beat_fixed_write sbfw ;
multi_beat_fixed_write mbfw ;
multi_beat_incr_write  mbiw  ;
multi_beat_wrap_write  mbww  ;

single_beat_fixed_read sbfr   ;
multi_beat_fixed_read mbfr   ;
multi_beat_incr_read  mbir    ;
multi_beat_wrap_read  mbwr    ;

invalid_wstrb          inv_wstrb   ; 
invalid_burst          inv_burst   ; 
misaligned_addr        mis_addr ; 

function new(input string name = "axi4_test", uvm_component parent = null);
    super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    env = axi4_env::type_id::create("env", this);

    sbfw      = single_beat_fixed_write::type_id::create("single_beat_fixed_write");
    mbfw      = multi_beat_fixed_write::type_id::create("multi_beat_fixed_write");
    mbiw      = multi_beat_incr_write::type_id::create("multi_beat_incr_write");
    mbww      = multi_beat_wrap_write::type_id::create("multi_beat_wrap_write");
    sbfr      = single_beat_fixed_read::type_id::create("single_beat_fixed_read");
    mbfr      = multi_beat_fixed_read::type_id::create("multi_beat_fixed_read");
    mbir      = multi_beat_incr_read::type_id::create("multi_beat_incr_read");
    mbwr      = multi_beat_wrap_read::type_id::create("multi_beat_wrap_read");
    inv_wstrb = invalid_wstrb::type_id::create("invalid_wstrb");
    inv_burst = invalid_burst::type_id::create("invalid_burst");
    mis_addr  = misaligned_addr::type_id::create("misaligned_addr");
endfunction


virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    sbfw.start(env.agent.seqr);
    #10;
    mbfw.start(env.agent.seqr); 
    #50;
    
    mbfw.start(env.agent.seqr);
    #10;
    mbfr.start(env.agent.seqr); 
    #50;
    
    mbiw.start(env.agent.seqr); 
    #10;
    mbir.start(env.agent.seqr);  
    #50;
    
    mbww.start(env.agent.seqr); 
    #10;
    mbwr.start(env.agent.seqr);  
    #50;
    
    inv_wstrb.start(env.agent.seqr);          
    #50;
    inv_burst.start(env.agent.seqr);          
    #50;
    mis_addr.start(env.agent.seqr);
    #50;
    phase.drop_objection(this);
endtask

endclass