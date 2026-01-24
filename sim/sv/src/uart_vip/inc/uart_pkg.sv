package uart_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // Define
    `include "uart_define.sv"
    `include "uart_configuration.sv"

    // UART TX components
    `include "uart_tx_transaction.sv"
    `include "uart_tx_driver.sv"
    `include "uart_tx_monitor.sv"
    `include "uart_tx_sequencer.sv"
    `include "uart_tx_agent.sv"

    // UART RX components 
    `include "uart_rx_transaction.sv"
    `include "uart_rx_driver.sv"
    `include "uart_rx_monitor.sv"
    `include "uart_rx_sequencer.sv"
    `include "uart_rx_agent.sv"

    `include "uart_virtual_sequencer.sv"

endpackage : uart_pkg