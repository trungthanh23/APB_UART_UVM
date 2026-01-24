package uart_apb_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    import apb_pkg::*;
    import uart_pkg::*;

    `include "apb_define.sv" 
    `include "apb_base_seq.sv"   
    `include "uart_tx_seq.sv"
    `include "uart_rx_seq.sv"

    `include "uart_apb_scoreboard.sv"

    `include "uart_apb_env_base.sv"
    `include "uart_apb_test_libs.sv" 

endpackage : uart_apb_pkg