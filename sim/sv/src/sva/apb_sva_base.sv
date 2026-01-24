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

    assert property (APB_RESET_p)
                    else `uvm_error("APB_SVA", "Reset error!");
    assert property (APB_SETUP_TO_ACCESS_p)
                    else `uvm_error("APB_SVA", "Wrong spec: APB don't change SETUP to ACCESS");
    assert property (APB_PENABLE_VALID_p)
                    else `uvm_error("APB_SVA", "Wrong spec: penable == 1 but psel != 1");
    assert property (APB_ADDR_CONTROL_STABLE_p)
                    else `uvm_error("APB_SVA", "Wrong spec: paddr and pwrtie no stable");
    assert property (APB_WDATA_STABLE_p)
                    else `uvm_error("APB_SVA", "Wrong spec: write mode but pwdata and pstrb no stable");
    assert property (APB_READ_STRB_LOW_p)
                    else `uvm_error("APB_SVA", "Wrong spec: read mode but pstrb != 0");
    assert property (APB_WRITE_STRB_VALID_p)
                    else `uvm_error("APB_SVA", "Wrong spec: write mode but pstrb have x and z");

endmodule