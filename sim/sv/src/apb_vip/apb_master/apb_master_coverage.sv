class apb_master_coverage extends uvm_subscriber #(apb_master_transaction);
    `uvm_component_utils(apb_master_coverage)

    apb_master_transaction tr;

    covergroup apb_master_cg;
        // Check Read and Write operations
        ADDR_CP: coverpoint tr.apb_addr[0] {
            bins tx_data_reg = {12'h0};
            bins rx_data_reg = {12'h4};
            bins cfg_reg     = {12'h8};
            bins ctrl_reg    = {12'hC};
            bins stt_reg     = {12'h10};
            illegal_bins illegal_addr = default;
        }

        WRITE_CP: coverpoint tr.apb_write[0] {
            bins write = {1'b1};
            bins read  = {1'b0};
        }

        // Check if all bytes are enabled during access
        STRB_CP: coverpoint tr.apb_strb[0] {
            bins full_access = {4'b1111};
            //bins partial     = {[4'b0001 : 4'b1110]};
        }

        // Monitor Slave Error responses
        ERROR_CP: coverpoint tr.apb_pslverr[0] {
            bins no_error = {1'b0};
            bins error    = {1'b1};
        }

        // Cross coverage: Ensure every register is both read and written
        ADDR_X_WRITE: cross ADDR_CP, WRITE_CP;

    endgroup

    function new(string name = "apb_master_coverage", uvm_component parent);
        super.new(name, parent);
        apb_master_cg = new();
    endfunction : new

    virtual function void write(apb_master_transaction t);
        this.tr = t;
        apb_master_cg.sample();
    endfunction : write

    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("COV_REPORT", $sformatf("APB Master Functional Coverage: %0.2f%%", apb_master_cg.get_inst_coverage()), UVM_LOW)
    endfunction : report_phase

endclass : apb_master_coverage