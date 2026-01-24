`uvm_analysis_imp_decl(_apb)     
`uvm_analysis_imp_decl(_uart_rx)  
`uvm_analysis_imp_decl(_uart_tx)  

class uart_apb_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(uart_apb_scoreboard)

  bit [7:0] q_expect_dut_tx[$]; 
  bit [7:0] q_actual_dut_tx[$]; 

  bit [7:0] q_expect_dut_rx[$];  
  bit [7:0] q_actual_dut_rx[$];  


  uvm_analysis_imp_apb     #(apb_master_transaction, uart_apb_scoreboard) apb_imp;
  uvm_analysis_imp_uart_rx #(uart_rx_transaction,       uart_apb_scoreboard) uart_rx_imp;
  uvm_analysis_imp_uart_tx #(uart_tx_transaction,       uart_apb_scoreboard) uart_tx_imp;

  function new(string name="uart_apb_scoreboard", uvm_component parent);
    super.new(name,parent);
  endfunction 

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    apb_imp     = new("apb_imp", this);
    uart_rx_imp = new("uart_rx_imp", this);
    uart_tx_imp = new("uart_tx_imp", this);
  endfunction

  virtual function void write_apb(apb_master_transaction item);
    if (item.apb_write[0] == 1'b1 && item.apb_addr[0] == 12'h000) begin
        `uvm_info("SCB_APB_WR", $sformatf("Expect DUT TX Send: 0x%0h", item.apb_data[0][7:0]), UVM_MEDIUM)
        q_expect_dut_tx.push_back(item.apb_data[0][7:0]);
    end
    else if (item.apb_write[0] == 1'b0 && item.apb_addr[0] == 12'h004) begin
        `uvm_info("SCB_APB_RD", $sformatf("Actual DUT RX Recive: 0x%0h", item.apb_data[0][7:0]), UVM_MEDIUM)
        q_actual_dut_rx.push_back(item.apb_data[0][7:0]);
    end
  endfunction : write_apb

  // Write from rx vip 
  virtual function void write_uart_rx(uart_rx_transaction item);
    `uvm_info("SCB_UART_RX", $sformatf("Actual DUT TX Send: 0x%0h", item.uart_rx_data_frame), UVM_MEDIUM)
    q_actual_dut_tx.push_back(item.uart_rx_data_frame);
  endfunction : write_uart_rx

  // Write from tx vip 
  virtual function void write_uart_tx(uart_tx_transaction item);
    `uvm_info("SCB_UART_TX", $sformatf("Expect DUT RX Recive: 0x%0h", item.uart_tx_data_frame), UVM_MEDIUM)
    q_expect_dut_rx.push_back(item.uart_tx_data_frame);
  endfunction : write_uart_tx

  task run_phase(uvm_phase phase);
    fork
        check_dut_tx(); 
        check_dut_rx();
    join
  endtask : run_phase

  task check_dut_tx();
    bit [7:0] exp, act;
    forever begin
      wait(q_expect_dut_tx.size() > 0 && q_actual_dut_tx.size() > 0);
      exp = q_expect_dut_tx.pop_front();
      act = q_actual_dut_tx.pop_front();
      
      if (exp !== act) 
        `uvm_error("SCB_TX_FAIL", $sformatf("DUT TX Mismatch! APB Wrote: %0h, DUT Sent: %0h", exp, act))
      else 
        `uvm_info("SCB_TX_PASS", $sformatf("DUT TX Match Send: %0h", exp), UVM_LOW)
    end
  endtask

  task check_dut_rx();
    bit [7:0] exp, act;
    forever begin
      wait(q_expect_dut_rx.size() > 0 && q_actual_dut_rx.size() > 0);
      exp = q_expect_dut_rx.pop_front();
      act = q_actual_dut_rx.pop_front();
      
      if (exp !== act) 
        `uvm_error("SCB_RX_FAIL", $sformatf("DUT RX Mismatch! VIP Sent: %0h, APB Read: %0h", exp, act))
      else 
        `uvm_info("SCB_RX_PASS", $sformatf("DUT RX Match Recive: %0h", exp), UVM_LOW)
    end
  endtask

endclass