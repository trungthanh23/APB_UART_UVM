class apb_master_transaction extends uvm_sequence_item;
    // Bus length
    rand int        bus_len;

    // APB address
    rand apb_addr_t apb_addr[];

    // APB data
    rand apb_data_t apb_pwdata[];
    
    // APB strobe
    rand apb_strb_t apb_strb[];
    
    // APB read/write(0/1)
    rand logic      apb_write[];
    
    // APB delay time
    rand int        apb_delay[];

    // APB read data
    rand apb_data_t apb_prdata[];

    // APB error
    rand bit        apb_pslverr[];

    // UVM macros
    `uvm_object_utils_begin(apb_master_transaction)
        `uvm_field_int          (bus_len,       UVM_ALL_ON)
        `uvm_field_array_int    (apb_addr,      UVM_ALL_ON)
        `uvm_field_array_int    (apb_pwdata,      UVM_ALL_ON)
        `uvm_field_array_int    (apb_write,     UVM_ALL_ON)
        `uvm_field_array_int    (apb_strb,      UVM_ALL_ON)
        `uvm_field_array_int    (apb_delay,     UVM_ALL_ON)
        `uvm_field_array_int    (apb_prdata,    UVM_ALL_ON | UVM_READONLY)
        `uvm_field_array_int    (apb_pslverr,   UVM_ALL_ON | UVM_READONLY)
    `uvm_object_utils_end

    // Contraint
    // max array size
    constraint c_array_size {
        apb_addr.size()  == bus_len;
        apb_pwdata.size()  == bus_len;
        apb_write.size() == bus_len;
        apb_strb.size()  == bus_len;
        apb_delay.size()     == bus_len;
        apb_prdata.size()    == bus_len;
        apb_pslverr.size()   == bus_len;
    }

    // Bus lenght
    constraint c_bus_len_default {
        soft bus_len == 1;
        bus_len > 0;
        bus_len <= 16;
    }

    // Strobe in read
    constraint c_read_strb {
        foreach (apb_strb[i]) {
            if (apb_write[i] == 1'b0) {
                apb_strb[i] == '0;
            } else {
                soft apb_strb[i] == '1;
            }
        }
    }

    // Address map
    constraint c_valid_uart_addr {
        foreach (apb_addr[i]) {
            apb_addr[i] inside {12'h0, 12'h4, 12'h8, 12'hC, 12'h10}; 
        }
    }

    // APB delay
    constraint c_delay_default {
        foreach (apb_delay[i]) {
            soft apb_delay[i] == 0;
            apb_delay[i] inside {[0:50]};
        }
    }

    // Contructor
    function new(string name = "apb_master_transaction");
        super.new(name);
    endfunction : new

endclass : apb_master_transaction