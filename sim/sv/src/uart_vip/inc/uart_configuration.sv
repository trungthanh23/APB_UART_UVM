class uart_configuration extends uvm_object;

    //UART interface
    virtual uart_tx_if      tx_if;
    virtual uart_rx_if      rx_if;
    
    // Frequency 50 MHz
    int frequency = 50000000;
    
    // Baudrate
    int baudrate = `UART_BAUDRATE_115200;
    
    // The number of data bits
    data_bit_num_e data_bit_num = UART_8BIT;
    
    // The number of stop bits
    stop_bit_num_e stop_bit_num = UART_ONE_STOP_BIT;
    
    // Parity enable
    parity_en_e parity_en = UART_PARITY_EN;
    
    // Parity type select
    parity_type_e parity_type = UART_PARITY_EVEN;
    
    //Set ACTIVE for tx to have driver, monitor, sequencer
    uvm_active_passive_enum is_active = UVM_ACTIVE;

    bit disable_parity_check_error = 0;
    bit expect_parity_error = 0;

    // UVM macros
    `uvm_object_utils_begin(uart_configuration)
      `uvm_field_enum        (data_bit_num_e,           data_bit_num,                   UVM_ALL_ON)
      `uvm_field_enum        (stop_bit_num_e,           stop_bit_num,                   UVM_ALL_ON)
      `uvm_field_enum        (parity_en_e,              parity_en,                      UVM_ALL_ON)
      `uvm_field_enum        (parity_type_e,            parity_type,                    UVM_ALL_ON)
      `uvm_field_enum        (uvm_active_passive_enum,  is_active,                      UVM_ALL_ON)
      `uvm_field_int         (                          disable_parity_check_error,     UVM_ALL_ON)
      `uvm_field_int         (                          expect_parity_error,            UVM_ALL_ON)
    `uvm_object_utils_end

    // Contructor
    function new (string name = "uart_configuration");
        super.new(name);
    endfunction : new

endclass : uart_configuration