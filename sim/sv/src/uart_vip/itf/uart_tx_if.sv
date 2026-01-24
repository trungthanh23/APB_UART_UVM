`include "uart_define.sv"
interface uart_tx_if();
    logic       clk;
    logic       reset_n;
    logic       tx;
    logic       cts_n;
    logic [7:0] tx_data;
    logic       tx_done;
    logic       start_tx;

    uart_data_frame_t uart_frame_tx;

    clocking driver_tx_cb @(posedge clk);
        default input #0 output #0;
        input   cts_n;
        output  tx;
    endclocking
    
    modport driver_tx_mp (
        input   cts_n,
        output  tx
    );
endinterface