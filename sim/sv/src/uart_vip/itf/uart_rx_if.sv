`include "uart_define.sv"
interface uart_rx_if();
    logic       clk;
    logic       reset_n;
    logic       rx;
    logic       rts_n;
    logic [7:0] rx_data;
    logic       rx_done;

    uart_data_frame_t uart_frame_rx;

    clocking driver_rx_cb @(posedge clk);
        default input #0 output #0;
        input   rx;
        output  rts_n;
    endclocking
    
    modport driver_rx_mp (
        input   rx,
        output  rts_n
    );
endinterface