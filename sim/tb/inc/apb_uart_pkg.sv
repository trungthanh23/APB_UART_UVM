package apb_uart_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    import apb_pkg::*;
    import uart_pkg::*;

    `include "apb_define.sv" 
    `include "apb_base_seq.sv"   
    `include "uart_tx_seq.sv"
    `include "uart_rx_seq.sv"

    `include "apb_uart_scoreboard.sv"

    `include "apb_uart_env_base.sv"
    `include "apb_uart_test_libs.sv" 

endpackage : apb_uart_pkg