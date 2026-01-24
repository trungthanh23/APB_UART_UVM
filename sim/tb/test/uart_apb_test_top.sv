`include "apb_sva_base.sv"
`include "uart_tx_sva_base.sv"
`include "uart_rx_sva_base.sv"
module uart_apb_test_top;
    import uvm_pkg::*;
    import uart_apb_pkg::*;

    logic clk_uart, clk_apb, reset_n;

    // Instantiation of interfaces 
    apb_master_itf apb_if();
    uart_rx_if     rx_if();
    uart_tx_if     tx_if();

    // SVA
    apb_sva_base        apb_sva(.apb_itf(apb_if));
//    uart_tx_sva_base    uart_tx_sva(.tx_if(tx_if));
//    uart_rx_sva_base    uart_rx_sva(.rx_if(rx_if));

    // DUT instantiation 
    uart dut (
        .clk        (clk_apb),
        .reset_n    (reset_n),
        .pclk       (clk_apb),
        .preset_n   (reset_n),
        .paddr      (apb_if.paddr),
        .prdata     (apb_if.prdata),
        .pwdata     (apb_if.pwdata),
        .psel       (apb_if.psel),
        .penable    (apb_if.penable),
        .pwrite     (apb_if.pwrite),
        .pstrb      (apb_if.pstrb),
        .pready     (apb_if.pready),
        .pslverr    (apb_if.pslverr),
        .rx         (tx_if.tx),
        .tx         (rx_if.rx),
        .cts_n      (rx_if.rts_n),
        .rts_n      (tx_if.cts_n)
    );

    assign rx_if.rx_done  = dut.rx_done;
    assign tx_if.tx_done  = dut.tx_done;
    assign tx_if.start_tx = dut.start_tx;
    assign apb_if.pclk    = clk_apb;
    assign apb_if.presetn = reset_n;
    assign rx_if.clk      = clk_uart;
    assign rx_if.reset_n  = reset_n;
    assign tx_if.clk      = clk_uart;
    assign tx_if.reset_n  = reset_n;

    // Clock and Reset generation
    initial begin
        clk_apb = 0;
        forever #10ns clk_apb = ~clk_apb;
    end

    initial begin
        clk_uart = 0;
        forever #10ns clk_uart = ~clk_uart;
    end

    initial begin
        reset_n = 1;
        #30ns reset_n = 0;
        #60ns reset_n = 1;
    end

    initial begin
        // Passing interfaces to the test 
        uvm_config_db#(virtual apb_master_itf)::set(null, "uvm_test_top", "apb_m_if", apb_if);
        uvm_config_db#(virtual uart_rx_if)::set(null, "uvm_test_top", "rx_if", rx_if);
        uvm_config_db#(virtual uart_tx_if)::set(null, "uvm_test_top", "tx_if", tx_if);
        run_test();
        $finish;
    end
endmodule