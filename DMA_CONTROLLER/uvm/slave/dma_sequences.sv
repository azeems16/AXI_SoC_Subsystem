class simple_write extends uvm_sequence#(dma_txn#(32,32))
`uvm_object_utils(simple_write)

dma_txn#(32,32) tr;

function new(input string name = "simple_write");
    super.new(name);
endfunction

virtual task body();
    repeat(5)
        begin
            tr = dma_txn#(32,32)::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize() with {
                is_write ==  1;
                wstrb    == '1;
            });
            finish_item(tr);
        end 
endtask

endclass

class simple_read extends uvm_sequence#(dma_txn#(32,32))
`uvm_object_utils(simple_read)

dma_txn#(32,32) tr;

function new(input string name = "simple_read");
    super.new(name);
endfunction

virtual task body();
    repeat(5)
        begin
            tr = dma_txn#(32,32)::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize() with {
                is_write ==  0;
            });
            finish_item(tr);
        end 
endtask

endclass

class random_write extends uvm_sequence#(dma_txn#(32,32))
`uvm_object_utils(random_write)

dma_txn#(32,32) tr;

function new(input string name = "random_write");
    super.new(name);
endfunction

virtual task body();
    repeat(5)
        begin
            tr = dma_txn#(32,32)::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize() with {
                is_write ==  1;
            });
            finish_item(tr);
        end 
endtask

endclass

class random_read extends uvm_sequence#(dma_txn#(32,32))
`uvm_object_utils(random_read)

dma_txn#(32,32) tr;

function new(input string name = "random_read");
    super.new(name);
endfunction

virtual task body();
    repeat(5)
        begin
            tr = dma_txn#(32,32)::type_id::create("tr");
            start_item(tr);
            assert(tr.randomize() with {
                is_write ==  0;
            });
            finish_item(tr);
        end 
endtask

endclass
