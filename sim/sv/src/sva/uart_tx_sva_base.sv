`include "uart_define.sv"

module uart_tx_sva_base (uart_tx_if tx_if);

    import uvm_pkg::*;         
    `include "uvm_macros.svh"

    logic clk;
    logic reset_n;
    logic start_tx;
    logic tx_done;
    logic cts_n;
    logic tx;

    assign clk          = tx_if.clk;
    assign reset_n      = tx_if.reset_n;
    assign start_tx     = tx_if.start_tx;
    assign tx_done      = tx_if.tx_done;
    assign cts_n        = tx_if.cts_n;
    assign tx           = apb_uart_test_top.dut.tx;
    assign dut_clk_tx   = apb_uart_test_top.dut.clk_tx;

    // Property
    property TX_RESET_DEFAULT_p;
        @(posedge clk) 
        ($past(reset_n) == 0) |-> (tx == 1'b1 && start_tx == 1'b0 && tx_done == 1'b1);
    endproperty

    property START_TX_CLEARS_IMMEDIATELY_p;
        @(posedge clk) disable iff (!reset_n)
        ($fell(tx) && start_tx) |-> (start_tx == 1'b0);
    endproperty

    property TX_DONE_FALLS_AFTER_START_BIT_p;
        @(negedge dut_clk_tx) disable iff (!reset_n)
        ($fell(tx) && start_tx) |=> (tx_done == 1'b0);
    endproperty

    // ASSERTIONS
    CHECK_RESET: assert property (TX_RESET_DEFAULT_p)
                 else `uvm_error("UART_TX_SVA", "\nReset error! Signals not default\n");

    CHECK_START_CLEAR: assert property (START_TX_CLEARS_IMMEDIATELY_p) 
                       else `uvm_error("UART_TX_SVA", "\nLogic Error: start_tx must be 0 immediately when TX starts!\n");

    CHECK_TX_DONE_TIMING: assert property (TX_DONE_FALLS_AFTER_START_BIT_p) 
                          else `uvm_error("UART_TX_SVA", "\nTiming Error: tx_done must go LOW only AFTER Start Bit finishes!\n");

endmodule