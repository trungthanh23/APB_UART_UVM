`include "apb_define.sv"
module apb_sva_base (apb_master_itf apb_itf);

    import uvm_pkg::*;        
    `include "uvm_macros.svh"

    logic                         apb_pclk;
    logic                         apb_presetn;
    logic [`APB_ADDR_WIDTH-1:0]   apb_paddr;
    logic [`APB_DATA_WIDTH-1:0]   apb_prdata;
    logic [`APB_DATA_WIDTH-1:0]   apb_pwdata;
    logic [`APB_STRB_WIDTH-1:0]   apb_pstrb;
    logic                         apb_psel;
    logic                         apb_penable;
    logic                         apb_pwrite;
    logic                         apb_pready;
    logic                         apb_pslverr;

    assign apb_pclk    = apb_itf.pclk;
    assign apb_presetn = apb_itf.presetn;
    assign apb_paddr   = apb_itf.paddr;
    assign apb_prdata  = apb_itf.prdata;
    assign apb_pwdata  = apb_itf.pwdata;
    assign apb_pstrb   = apb_itf.pstrb;
    assign apb_psel    = apb_itf.psel;
    assign apb_penable = apb_itf.penable;
    assign apb_pwrite  = apb_itf.pwrite;
    assign apb_pready  = apb_itf.pready;
    assign apb_pslverr = apb_itf.pslverr;   

    // Property
    property APB_RESET_p;
        @(posedge apb_pclk)
        ($past(apb_presetn) == 0) |-> (apb_psel == 0 && apb_penable == 0);
    endproperty

    property APB_SETUP_TO_ACCESS_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && !apb_penable) |=> (apb_psel && apb_penable);
    endproperty

    property APB_PENABLE_VALID_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        apb_penable |-> apb_psel;
    endproperty

    property APB_ADDR_CONTROL_STABLE_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && !apb_pready) |=> ($stable(apb_paddr) && $stable(apb_pwrite));
    endproperty

    property APB_WDATA_STABLE_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_pwrite && !apb_pready) |=> ($stable(apb_pwdata) && $stable(apb_pstrb));
    endproperty

    property APB_READ_STRB_LOW_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && !apb_pwrite) |-> (apb_pstrb == 0);
    endproperty

    property APB_WRITE_STRB_VALID_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_pwrite) |-> (!$isunknown(apb_pstrb));
    endproperty

    property CHECK_TX_DATA_WR_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_penable && apb_pwrite && apb_pready && apb_paddr == 12'h000)
        |=> (apb_uart_test_top.dut.tx_data == $past(apb_pwdata[7:0]));
    endproperty

    property CHECK_CFG_DATA_BIT_WR_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_penable && apb_pwrite && apb_pready && apb_paddr == 12'h008)
        |=> (apb_uart_test_top.dut.data_bit_num == $past(apb_pwdata[1:0]));
    endproperty

    property CHECK_CFG_STOP_BIT_WR_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_penable && apb_pwrite && apb_pready && apb_paddr == 12'h008)
        |=> (apb_uart_test_top.dut.stop_bit_num == $past(apb_pwdata[2]));
    endproperty

    property CHECK_CFG_PARITY_EN_WR_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_penable && apb_pwrite && apb_pready && apb_paddr == 12'h008)
        |=> (apb_uart_test_top.dut.parity_en == $past(apb_pwdata[3]));
    endproperty

    property CHECK_CFG_PARITY_TYPE_WR_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_penable && apb_pwrite && apb_pready && apb_paddr == 12'h008)
        |=> (apb_uart_test_top.dut.parity_type == $past(apb_pwdata[4]));
    endproperty

    property CHECK_CTRL_START_TX_WR_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_penable && apb_pwrite && apb_pready && apb_paddr == 12'h00C)
        |=> (apb_uart_test_top.dut.start_tx == $past(apb_pwdata[0]));
    endproperty

    property ERR_WRITE_RO_RX_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_penable && apb_pwrite && apb_pready && apb_paddr == 12'h004)
        |-> (apb_pslverr == 1'b1);
    endproperty

    property ERR_WRITE_INVALID_ADDR_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_penable && apb_pwrite && apb_pready && 
        !(apb_paddr inside {12'h000, 12'h008, 12'h00C}))
        |-> (apb_pslverr == 1'b1);
    endproperty

    property ERR_WRITE_VALID_ADDR_p;
        @(posedge apb_pclk) disable iff (!apb_presetn)
        (apb_psel && apb_penable && apb_pwrite && apb_pready && 
        (apb_paddr inside {12'h000, 12'h008, 12'h00C}))
        |-> (apb_pslverr == 1'b0);
    endproperty

    // Assertion
    APB_RESET: assert property (APB_RESET_p)
                    else `uvm_error("APB_SVA", "\nReset error!\n");

    APB_SETUP_TO_ACCESS: assert property (APB_SETUP_TO_ACCESS_p)
                    else `uvm_error("APB_SVA", "\nWrong spec: APB don't change SETUP to ACCESS\n");

    APB_PENABLE_VALID: assert property (APB_PENABLE_VALID_p)
                    else `uvm_error("APB_SVA", "\nWrong spec: penable == 1 but psel != 1\n");

    APB_ADDR_CONTROL_STABLE: assert property (APB_ADDR_CONTROL_STABLE_p)
                    else `uvm_error("APB_SVA", "\nWrong spec: paddr and pwrtie no stable\n");

    APB_WDATA_STABLE: assert property (APB_WDATA_STABLE_p)
                    else `uvm_error("APB_SVA", "\nWrong spec: write mode but pwdata and pstrb no stable\n");

    APB_READ_STRB_LOW: assert property (APB_READ_STRB_LOW_p)
                    else `uvm_error("APB_SVA", "\nWrong spec: read mode but pstrb != 0\n");

    APB_WRITE_STRB_VALID: assert property (APB_WRITE_STRB_VALID_p)
                    else `uvm_error("APB_SVA", "\nWrong spec: write mode but pstrb have x and z\n");

    ASSERT_TX_DATA: assert property (CHECK_TX_DATA_WR_p)
                    else `uvm_error("APB_SVA", "\nTX_DATA register update failed\n");

    ASSERT_CFG_DATA_BIT: assert property (CHECK_CFG_DATA_BIT_WR_p)
                    else `uvm_error("APB_SVA", "\nCONFIG data_bit_num update failed\n");

    ASSERT_CFG_STOP_BIT: assert property (CHECK_CFG_STOP_BIT_WR_p)
                    else `uvm_error("APB_SVA", "\nCONFIG stop_bit_num update failed\n");

    ASSERT_CFG_PARITY_EN: assert property (CHECK_CFG_PARITY_EN_WR_p)
                    else `uvm_error("APB_SVA", "\nCONFIG parity_en update failed\n");

    ASSERT_CFG_PARITY_TYPE: assert property (CHECK_CFG_PARITY_TYPE_WR_p)
                    else `uvm_error("APB_SVA", "\nCONFIG parity_type update failed\n");

    ASSERT_CTRL_START_TX: assert property (CHECK_CTRL_START_TX_WR_p)
                    else `uvm_error("APB_SVA", "\nCONTROL start_tx update failed\n");

    CHECK_ERR_RO_RX: assert property (ERR_WRITE_RO_RX_p)
                    else `uvm_error("APB_SVA", "\nWrite to RO Register (RX) did NOT assert PSLVERR!\n");

    CHECK_ERR_INVALID: assert property (ERR_WRITE_INVALID_ADDR_p)
                    else `uvm_error("APB_SVA", "\nWrite to Invalid Address did NOT assert PSLVERR!\n");

    CHECK_OK_VALID: assert property (ERR_WRITE_VALID_ADDR_p)
                    else `uvm_error("APB_SVA", "\nValid Write asserted PSLVERR unexpectedly!\n");

endmodule