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

    assign clk      = tx_if.clk;
    assign reset_n  = tx_if.reset_n;
    assign start_tx = tx_if.start_tx;
    assign tx_done  = tx_if.tx_done;
    assign cts_n    = tx_if.cts_n;
    assign tx       = tx_if.tx;

    property TX_RESET_DEFAULT_p;
        @(posedge clk) 
        ($past(reset_n) == 0) |-> (tx == 1'b1 && start_tx == 1'b0 && tx_done == 1'b1);
    endproperty

    property TX_START_CLEARS_DONE_p;
        @(posedge clk) disable iff (!reset_n)
        $rose(start_tx) |=> (tx_done == 1'b0);
    endproperty

    property TX_WAIT_CTS_p;
        @(posedge clk) disable iff (!reset_n)
        (tx_done == 1'b1 && start_tx && cts_n == 1'b1) |-> (tx == 1'b1);
    endproperty

    CHECK_RESET:        assert property (TX_RESET_DEFAULT_p)
                        else `uvm_error("UART_TX_SVA", "Reset error! tx_done should be 1, tx should be 1");
    CHECK_START_BUSY:   assert property (TX_START_CLEARS_DONE_p) 
                        else `uvm_error("UART_TX_SVA", "Wrong spec: start_tx == 1 but tx_done != 0");
    CHECK_FLOW_CTRL:    assert property (TX_WAIT_CTS_p) 
                        else `uvm_error("UART_TX_SVA", "Wrong spec: cts_n = 1 but tx != 1");

endmodule