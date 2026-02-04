`include "uart_define.sv"

module uart_rx_sva_base (uart_rx_if rx_if);

    import uvm_pkg::*;         
    `include "uvm_macros.svh"

    logic clk;
    logic reset_n;
    logic rx;
    logic rts_n;
    logic rx_done;

    assign clk      = rx_if.clk;
    assign reset_n  = rx_if.reset_n;
    assign rx       = rx_if.rx;
    assign rts_n    = rx_if.rts_n; 
    assign rx_done  = rx_if.rx_done; 

    property RX_RESET_DEFAULT_p;
        @(posedge clk) 
        ($past(reset_n) == 0) |-> (rts_n == 1'b1 && rx == 1);
    endproperty

    // property RX_BUSY_WHEN_DONE_p;
    //     @(posedge clk) disable iff (!reset_n)
    //     (rx_done == 1'b1) |-> (rts_n == 1'b1);
    // endproperty

    // property RX_READY_AFTER_READ_p;
    //     @(posedge clk) disable iff (!reset_n)
    //     $fell(rx_done) |=> (rts_n == 1'b0);
    // endproperty

    property CHECK_STOP_BIT_HIGH_p;
        @(posedge clk) disable iff (!reset_n)
        $rose(rx_done) |-> (rx == 1'b1); 
    endproperty

    CHECK_RX_RESET:             assert property (RX_RESET_DEFAULT_p) 
                                else `uvm_error("UART_RX_SVA", "Reset error! rts_n should be 0 (ready)");
    
    // CHECK_RX_BUSY:              assert property (RX_BUSY_WHEN_DONE_p) 
    //                             else `uvm_error("UART_RX_SVA", "Wrong spec: rx_done = 1 but rts_n != 1 (Busy)");
    
    // CHECK_RX_READY:             assert property (RX_READY_AFTER_READ_p) 
    //                             else `uvm_error("UART_RX_SVA", "Wrong spec: rx_done fell but rts_n != 0 (Ready)");

    ASSERT_DUT_TX_STOP_BIT:     assert property (CHECK_STOP_BIT_HIGH_p)
                                else `uvm_error("UART_PHY_SVA", "DUT TX Stop Bit is not 1 (Framing Error)!");

endmodule