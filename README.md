# APB-UART UVM Verification Environment

![UVM Architecture](APB_UART_UVM_Env.jpg)

## 📌 Overview
This project implements a **UVM (Universal Verification Methodology)** testbench to verify an **APB-UART Bridge** Design Under Test (DUT).

The DUT acts as a bridge between an APB Bus (connected to a CPU) and a UART Interface (connected to peripheral devices). The verification environment is designed to verify Functional correctness, Protocol compliance, and Error handling capabilities using a **Black-box** approach.

## 🛠 DUT Features
Based on the specification, the APB-UART Bridge supports:
* **Interfaces:** APB Slave (Host side) & UART (TX/RX, RTS/CTS flow control).
* **Configurable Data Frame:**
    * Data bits: 5, 6, 7, 8 bits.
    * Parity: None, Odd, Even.
    * Stop bits: 1, 2 bits.
* **Baud Rate:** Configurable via clock frequency dividers.
* **Register Map:**
    * `TX_DATA` (0x00): Transmit Data.
    * `RX_DATA` (0x04): Receive Data (Read-Only).
    * `CFG_REG` (0x08): Configuration (Data bits, Parity, Stop bits).
    * `CTRL_REG` (0x0C): Control (Start TX).
    * `STT_REG` (0x10): Status (TX Done, RX Done, Parity Error).

## 🏗 Verification Architecture
The UVM Environment consists of the following components:

| Component | Description |
| :--- | :--- |
| **APB Master VIP** | Acts as the host CPU, performing Register Read/Write operations on the APB bus. |
| **UART TX/RX VIP** | Acts as the peripheral device. **RX VIP** drives data into DUT; **TX VIP** monitors data coming from DUT. |
| **Scoreboard** | Compares data integrity between APB and UART interfaces. Includes logic to mask data bits based on configuration (5/6/7-bit modes). |
| **Coverage** | Collects Functional Coverage for Register Access (`ADDR_CP`, `WRITE_CP`) and Cross Coverage. |
| **SVA (Assertions)** | Checks APB Protocol timing, UART Physical Layer (Start/Stop bits), and Register update logic. |

## 🧪 Test Scenarios
The following tests are implemented in `apb_uart_test_libs.sv`:

| Test Name | Description |
| :--- | :--- |
| **Sanity Tests** | |
| `apb_uart_simple_test` | Basic data transfer check (APB Write -> UART TX, UART RX -> APB Read). |
| `apb_simple_write_test` | Verifies basic APB Write protocol. |
| **Functional Tests** | |
| `uart_tx_rand_cfg_test` | Randomizes configuration (Data bits, Parity, Stop bits) with **History Queue** to ensure unique coverage. |
| `apb_uart_full_duplex_test` | Stress test: Runs TX and RX transactions simultaneously (Full Duplex). |
| `apb_config_readback_test` | Writes to Configuration registers and reads back to verify data integrity. |
| **Error Injection Tests** | |
| `apb_write_addr_error_test` | Checks DUT behavior on Invalid Address access, RO Register writes, and **Address Aliasing**. |
| `uart_tx_parity_error_test` | Injects Parity Error from VIP to verify if DUT sets the `parity_error` flag in Status Register. |
| `uart_tx_glitch_test` | Injects Glitch (short pulse) on RX line to verify DUT's noise rejection capability. |
| `apb_uart_reset_registers_test` | **Reset-on-the-fly:** Asserts Hardware Reset during an active transfer to verify recovery. |

## 🚀 How to Run

This project requires **Mentor Graphics QuestaSim**.

### 1. Environment Setup
Before running, you must configure the paths in the `qrun_bash.sh` file to match your local installation.

Open `qrun_bash.sh` and edit the following lines:

```bash
# Example paths - Change these to match your system
export UVM_HOME=/home/thanhtrung/Tools/Questasim/questasim/verilog_src/uvm-1.2
export LM_LICENSE_FILE=/home/thanhtrung/Tools/Questasim/questasim/LICENSE.dat
export MTI_HOME=/home/thanhtrung/Tools/Questasim/questasim
2. Execution Steps
Follow these steps to compile and run the simulation:

Navigate to the simulation working directory:

Bash
cd sim/work
Source the setup script:

Bash
source ../../qrun_bash.sh
Run the simulation commands (Library creation, Compilation, Simulation):

Bash
vlb; vlg; vsm
(Note: vlb, vlg, vsm are aliases defined in the qrun_bash.sh script)

3. Run Specific Test
To run a specific test case (e.g., uart_tx_rand_cfg_test) with coverage enabled:

Bash
vsim -c apb_uart_test_top \
     -do "coverage save -onexit -assert -code bcefs -directive -cvg coverage.ucdb; add wave -r /*; run -all; quit" \
     +UVM_TESTNAME=uart_tx_rand_cfg_test
🐛 Bugs Found & Analysis
During verification, the following issues were identified in the Black-box design:

Parity Config Stuck: The parity_en bit in the Config register was stuck at 1.

Address Aliasing: Writing to address 0x108 incorrectly overwrote 0x08 (Decoding error).

Data Masking Issue: In 8-bit mode, the DUT incorrectly masked the MSB (Bit 7), treating data as 7-bit.

Project maintained by Thanh Trung.