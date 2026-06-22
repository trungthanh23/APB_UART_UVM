#!/usr/bin/tclsh

# List of all tests 
set all_tests {
    apb_uart_simple_test
    apb_simple_write_test
    apb_write_rand_cfg_test
    apb_write_addr_error_test
    apb_config_readback_test
    apb_full_coverage_test
    uart_tx_rand_cfg_test
    uart_tx_simple_test
    uart_tx_parity_error_test
    uart_tx_glitch_test
    apb_uart_full_duplex_test
    apb_uart_reset_registers_test
}

set bug_define ""
set test_name ""
set clean_run 0
set show_help 0

for {set i 0} {$i < [llength $argv]} {incr i} {
    set arg [lindex $argv $i]
    switch -exact -- $arg {
        "-bug" {
            incr i
            set bug_define [lindex $argv $i]
        }
        "-test" {
            incr i
            set test_name [lindex $argv $i]
        }
        "-clean" {
            set clean_run 1
        }
        "-help" - "-h" {
            set show_help 1
        }
        default {
            puts "Unknown argument: $arg"
            set show_help 1
        }
    }
}

if {$show_help} {
    puts "Usage: tclsh run_tests.tcl \[options\]"
    puts "Options:"
    puts "  -bug <name>    Inject bug define in hdl/uart.svp (e.g. BUG14, none to clear)"
    puts "  -test <name>   Run a specific test"
    puts "  -clean         Clean work directory and logs before running"
    puts "  -help          Show this help message"
    exit 0
}

# Update BUG define in uart.svp
if {$bug_define ne ""} {
    puts "======================================================================"
    puts "Injecting BUG define: $bug_define"
    puts "======================================================================"
    set svp_file "../../hdl/uart.svp"
    if {[file exists $svp_file]} {
        set fp [open $svp_file r]
        set file_data [read $fp]
        close $fp
        
        set lines [split $file_data "\n"]
        
        if {$bug_define eq "none"} {
            lset lines 0 "// `define NO_BUG"
        } else {
            lset lines 0 "`define $bug_define"
        }
        
        set fp [open $svp_file w]
        puts -nonewline $fp [join $lines "\n"]
        close $fp
        puts "Updated line 1 of $svp_file successfully."
    } else {
        puts "Error: $svp_file not found."
        exit 1
    }
}

# Clean directories
if {$clean_run} {
    puts "Cleaning work and log directories..."
    file delete -force work
    file delete -force log
}

# Re-create directories 
if {![file exists work]} {
    puts "Creating work library..."
    if {[catch {exec vlib work 2>@1} msg]} {
        puts "Error creating work library: $msg"
        exit 1
    }
}
if {![file exists log]} {
    file mkdir log
}

# Compile RTL and Testbench
puts "Compiling RTL..."
if {[catch {exec vlog -64 -f filelist_com.f -f filelist_rtl.f +cover=bcefs -l ./log/vlogr.log 2>@1} msg]} {
    puts "RTL Compilation failed! Check ./log/vlogr.log"
    puts $msg
    exit 1
}

puts "Compiling Testbench..."
if {[catch {exec vlog -64 -f filelist_com.f -f filelist_vsim.f -f filelist_tb.f -l ./log/vlogt.log 2>@1} msg]} {
    puts "Testbench Compilation failed! Check ./log/vlogt.log"
    puts $msg
    exit 1
}
puts "Compilation completed successfully."

set tests_to_run $all_tests
if {$test_name ne ""} {
    if {[lsearch -exact $all_tests $test_name] >= 0} {
        set tests_to_run [list $test_name]
    } else {
        puts "Error: Test '$test_name' is not in the list of available tests."
        puts "Available tests: [join $all_tests ", "]"
        exit 1
    }
}

# Execute Simulations
puts "======================================================================"
puts "Running [llength $tests_to_run] test(s)..."
puts "======================================================================"
set results [dict create]

set uvm_dpi_lib "uvm_dpi"
if {$tcl_platform(platform) eq "windows"} {
    set uvm_dpi_lib "C:/questasim64_2024.1/uvm-1.2/win64/uvm_dpi"
}

foreach test $tests_to_run {
    puts -nonewline "Running $test... "
    flush stdout
    
    set log_file "./log/vsim_${test}.log"
    set wlf_file "vsim_${test}.wlf"
    
    set cmd [list vsim -64 -c apb_uart_test_top -wlf $wlf_file -solvefaildebug -assertdebug -sva -coverage -voptargs=+acc -l $log_file +UVM_VERBOSITY=UVM_MEDIUM +UVM_TESTNAME=$test -sv_lib $uvm_dpi_lib -do "coverage save -onexit -assert -code bcefs -directive -cvg coverage.ucdb; add wave -r /apb_uart_test_top/*; run -all; quit"]
    
    if {[catch {eval exec $cmd 2>@1} sim_output]} {
    }
    
    set status "PASS"
    set fail_reason ""
    
    if {[file exists $log_file]} {
        set fp [open $log_file r]
        set log_content [read $fp]
        close $fp
        
        set has_uvm_error 0
        set has_uvm_fatal 0
        set has_sim_error 0
        set error_msgs [list]
        
        # Check Report Summary
        if {[regexp {Number of UVM_ERROR\s*:\s*([1-9]\d*)} $log_content -> err_count]} {
            set has_uvm_error 1
        }
        if {[regexp {Number of UVM_FATAL\s*:\s*([1-9]\d*)} $log_content -> fatal_count]} {
            set has_uvm_fatal 1
        }
        
        set lines [split $log_content "\n"]
        foreach line $lines {
            if {[regexp {^# \*\* (Error|Fatal|Failure):} $line]} {
                set has_sim_error 1
                set clean_line [regsub {^# } $line ""]
                lappend error_msgs $clean_line
            }
            if {[regexp {UVM_ERROR\s*@|UVM_FATAL\s*@} $line]} {
                set clean_line [regsub {^# } $line ""]
                lappend error_msgs $clean_line
            }
            if {[regexp {BUG DETECTED|mismatch|failure|FAIL} $line] && [regexp {UVM_ERROR|UVM_FATAL|Error} $line]} {
                set clean_line [regsub {^# } $line ""]
                if {[lsearch -exact $error_msgs $clean_line] == -1} {
                    lappend error_msgs $clean_line
                }
            }
        }
        
        if {$has_uvm_error || $has_uvm_fatal || $has_sim_error} {
            set status "FAIL"
            if {[llength $error_msgs] > 0} {
                set unique_errors [list]
                foreach err $error_msgs {
                    if {[lsearch -exact $unique_errors $err] == -1} {
                        lappend unique_errors $err
                    }
                }
                if {[llength $unique_errors] > 2} {
                    set unique_errors [lrange $unique_errors 0 1]
                    lappend unique_errors "... (more errors in log)"
                }
                set fail_reason [join $unique_errors " | "]
            } else {
                set fail_reason "UVM_ERROR or Simulation Error detected (check log)"
            }
        }
    } else {
        set status "FAIL"
        set fail_reason "Log file not generated"
    }
    
    puts $status
    dict set results $test status $status
    dict set results $test reason $fail_reason
}

# Report
puts "\n"
puts "=========================================================================================================="
puts "                                        REGRESSION RUN SUMMARY"
if {$bug_define ne ""} {
    puts "   BUG Define Tested: $bug_define"
} else {
    puts "   BUG Define Tested: (default)"
}
puts "=========================================================================================================="
puts [format "%-35s | %-8s | %-60s" "Test Name" "Status" "Fail Reason / Location"]
puts "----------------------------------------------------------------------------------------------------------"

set passed_count 0
set failed_count 0

dict for {test info} $results {
    set st [dict get $info status]
    set rs [dict get $info reason]
    if {$st eq "PASS"} {
        incr passed_count
    } else {
        incr failed_count
    }
    if {[string length $rs] > 60} {
        set rs "[string range $rs 0 56]..."
    }
    puts [format "%-35s | %-8s | %-60s" $test $st $rs]
}
puts "=========================================================================================================="
puts "   Passed: $passed_count, Failed: $failed_count, Total: [expr {$passed_count + $failed_count}]"
puts "=========================================================================================================="

if {$failed_count > 0} {
    exit 
} else {
    exit 0
}
