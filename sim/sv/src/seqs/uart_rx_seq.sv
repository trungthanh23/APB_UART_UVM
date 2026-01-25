class uart_rx_seq extends uvm_sequence #(uart_rx_transaction);
    `uvm_object_utils(uart_rx_seq)
    `uvm_declare_p_sequencer(uart_rx_sequencer) 

    uart_configuration  uart_rx_cfg;

    function new(string name = "uart_rx_seq");
        super.new(name);
    endfunction : new

    virtual task pre_start();
        super.pre_start();
        uart_rx_cfg = p_sequencer.uart_rx_cfg;
    endtask : pre_start

    virtual task body();
        forever begin
            req = uart_rx_transaction::type_id::create("req");
            `uvm_do(req)
        end
    endtask : body
    
endclass : uart_rx_seq