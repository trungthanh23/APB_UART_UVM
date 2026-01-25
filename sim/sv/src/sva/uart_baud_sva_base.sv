`include "uart_define.sv"

module uart_baud_sva_base (input logic clk_sys, input logic reset_n);

    import uvm_pkg::*;         
    `include "uvm_macros.svh"

    logic dut_clk_tx;
    logic dut_clk_rx;

    assign dut_clk_tx = apb_uart_test_top.dut.clk_tx;
    assign dut_clk_rx = apb_uart_test_top.dut.clk_rx;

    localparam int EXP_TX_CYCLES = 435;
    localparam int EXP_RX_CYCLES = 28;
    
    property check_cycles_p(logic dut_clk, int exp_cycles);
        int cnt;
        @(posedge dut_clk) disable iff (!reset_n)
        (1, cnt = 0) 
        |=> 
        (
            ( @(posedge clk_sys) (1, cnt = cnt + 1) )[*1:$]
            intersect 
            ( @(posedge dut_clk) 1'b1 )
        )
        |-> (cnt >= exp_cycles - 1 && cnt <= exp_cycles + 1);
        
    endproperty

    int cnt_tx;
    logic check_tx_en;
    
    always @(posedge clk_sys or negedge reset_n) begin
        if (!reset_n) begin
            cnt_tx <= 0;
            check_tx_en <= 0;
        end else begin
            if (dut_clk_tx) begin
                cnt_tx <= 1; 
                check_tx_en <= 1;
            end else begin
                cnt_tx <= cnt_tx + 1;
            end
        end
    end

    property p_check_tx_cycles;
        @(posedge clk_sys) disable iff (!reset_n || !check_tx_en)
        dut_clk_tx |-> ($past(cnt_tx) == EXP_TX_CYCLES);
    endproperty

    int cnt_rx;
    logic check_rx_en;

    always @(posedge clk_sys or negedge reset_n) begin
        if (!reset_n) begin
            cnt_rx <= 0;
            check_rx_en <= 0;
        end else begin
            if (dut_clk_rx) begin
                cnt_rx <= 1; 
                check_rx_en <= 1;
            end else begin
                cnt_rx <= cnt_rx + 1;
            end
        end
    end

    property p_check_rx_cycles;
        @(posedge clk_sys) disable iff (!reset_n || !check_rx_en)
        dut_clk_rx |-> ($past(cnt_rx) == EXP_RX_CYCLES);
    endproperty


    // --- ASSERTIONS ---
    CHECK_CLK_TX_CYCLES: assert property (p_check_tx_cycles)
        else `uvm_error("CLK_SVA", $sformatf("CLK_TX Cycle Count Wrong! Exp: %0d, Act: %0d", EXP_TX_CYCLES, $past(cnt_tx)));

    CHECK_CLK_RX_CYCLES: assert property (p_check_rx_cycles)
        else `uvm_error("CLK_SVA", $sformatf("CLK_RX Cycle Count Wrong! Exp: %0d, Act: %0d", EXP_RX_CYCLES, $past(cnt_rx)));

endmodule