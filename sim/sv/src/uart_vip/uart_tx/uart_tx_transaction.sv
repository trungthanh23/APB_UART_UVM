class uart_tx_transaction extends uvm_sequence_item;

    //UART TX configuration
    uart_configuration      uart_tx_cfg;
    rand uart_data_frame_t  uart_tx_data_frame;

    //UART TX error parity and stop
    rand bit inject_parity_error; 
    rand bit inject_stop_error;

    // UVM macros
    `uvm_object_utils_begin(uart_tx_transaction)
        `uvm_field_int(uart_tx_data_frame, UVM_ALL_ON)
        `uvm_field_int(inject_parity_error, UVM_ALL_ON)
        `uvm_field_int(inject_stop_error, UVM_ALL_ON)
    `uvm_object_utils_end

    //Constructor
    function new (string name = "uart_tx_transaction");
        super.new(name);
    endfunction : new

    //Pre randomize
    function void pre_randomize();
        `uvm_info(this.get_full_name(), "Pre-Randomize", UVM_HIGH);
        if (!uvm_config_db #(uart_configuration)::get(null, get_full_name(), "uart_tx_cfg", uart_tx_cfg) && uart_tx_cfg == null)
            `uvm_fatal("post_randomize", "Cannot get UART TX configuration in transaction")
    endfunction : pre_randomize

    //Post randomize
    function void post_randomize();
        `uvm_info(this.get_full_name(), "Post-Randomize", UVM_HIGH);
        
        //Change data to fit with config
        if (uart_tx_cfg.data_bit_num == UART_5BIT) begin
          uart_tx_data_frame[`UART_MAX_DATA_WIDTH - 1 : 5] = '0;
        end
        else if (uart_tx_cfg.data_bit_num == UART_6BIT) begin
          uart_tx_data_frame[`UART_MAX_DATA_WIDTH - 1 : 6] = '0;
        end
        else if (uart_tx_cfg.data_bit_num == UART_7BIT) begin
          uart_tx_data_frame[`UART_MAX_DATA_WIDTH - 1 : 7] = '0;
        end
    endfunction : post_randomize

endclass : uart_tx_transaction 