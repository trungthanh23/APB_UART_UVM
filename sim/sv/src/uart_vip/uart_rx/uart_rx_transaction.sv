class uart_rx_transaction extends uvm_sequence_item;

    //UART RX configuration
    uart_configuration      uart_rx_cfg;
    uart_data_frame_t       uart_rx_data_frame;

    //UART RX stop and parity bit error
    bit parity_error;
    bit stop_error;

    `uvm_object_utils_begin(uart_rx_transaction)
      `uvm_field_int    (uart_rx_data_frame, UVM_ALL_ON)
    `uvm_object_utils_end

    //Constructor
    function new (string name = "uart_rx_transaction");
        super.new(name);
    endfunction : new

endclass : uart_rx_transaction