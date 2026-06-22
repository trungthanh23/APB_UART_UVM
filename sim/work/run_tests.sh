#!/bin/bash
if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "cygwin" || "$OSTYPE" == "mingw"* ]]; then
    # For run in Win        
    export UVM_HOME="/c/questasim64_2024.1/verilog_src/uvm-1.2"
else
    export MTI_HOME=/home/thanhtrung/Tools/Questasim/questasim
    export PATH=$MTI_HOME/linux_x86_64:$PATH
    export LM_LICENSE_FILE=/home/thanhtrung/Tools/Questasim/questasim/LICENSE.dat
    export UVM_HOME=/home/thanhtrung/Tools/Questasim/questasim/verilog_src/uvm-1.2
fi

tclsh run_tests.tcl "$@"
