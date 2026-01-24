////////////////////////////////////////////////////////////////////////////////
//  Library Folder
////////////////////////////////////////////////////////////////////////////////
+incdir+$UVM_HOME/src
$UVM_HOME/src/uvm_pkg.sv
//  Global Defines and Global Params
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//  Include Directories
////////////////////////////////////////////////////////////////////////////////
// +incdir+../inc

// +incdir+../libs

// -y ../../libs
+incdir+../sv/src/apb_vip/inc
+incdir+../sv/src/apb_vip/apb_master
+incdir+../sv/src/uart_vip/inc
+incdir+../sv/src/uart_vip/uart_tx
+incdir+../sv/src/uart_vip/uart_rx
+incdir+../tb/inc
+incdir+../tb/test
+incdir+../sv/src/seqs
+incdir+../sv/src/sva

////////////////////////////////////////////////////////////////////////////////
//  Top Testbench Level Module
////////////////////////////////////////////////////////////////////////////////

// ../tb/uart_core_tb.sv
// ../tb/user_case_test_tx.sv
// ../tb/user_case_test_rx.sv
// ../tb/tx_block_tb.sv
// ../tb/rx_block_tb.sv
// ../tb/user_case_test_baud.sv
// ../tb/baudrate_gen_block_tb.sv
// ../tb/test.sv
// ../tb/_assertion.sv
// ../tb/assertion_ex.sv

../sv/src/apb_vip/inc/apb_define.sv
//../sv/src/uart_vip/inc/uart_define.sv

../sv/src/apb_vip/itf/apb_master_itf.sv
../sv/src/uart_vip/itf/uart_tx_if.sv
../sv/src/uart_vip/itf/uart_rx_if.sv
../sv/src/apb_vip/inc/apb_pkg.sv
../sv/src/uart_vip/inc/uart_pkg.sv
../tb/inc/uart_apb_pkg.sv
../tb/test/uart_apb_test_top.sv