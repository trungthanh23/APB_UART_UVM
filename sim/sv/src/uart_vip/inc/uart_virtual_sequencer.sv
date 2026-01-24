class uart_virtual_sequencer extends uvm_sequencer;
    `uvm_component_utils(uart_virtual_sequencer)

    uart_configuration  uart_cfg;
    uart_tx_sequencer   tx_seqr; 
    uart_rx_sequencer   rx_seqr;

    // Contructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        if (uart_cfg == null)
            `uvm_fatal("connect_phase", "Virtual sequencer cannot get env configuration object")
    
    endfunction : connect_phase
endclass : uart_virtual_sequencer