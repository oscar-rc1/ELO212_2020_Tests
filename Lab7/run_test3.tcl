cd [file dirname [info script]]

create_project -force Sesion7_ELO212_Test3 -part xc7a100tcsg324-1 vivado/test3

read_verilog -sv tb/tb_act3.sv
read_verilog -sv ../Modules/calc_fsm.sv
read_verilog -sv ../Modules/sseg_decoder.sv
read_verilog -sv ../ExtModules/ALU_ref/ALU_ref.sv
read_verilog -sv ../ExtModules/double-dabble-32bits/unsigned_to_bcd.v
read_verilog -sv [glob ../ExtModules/PushButton-debouncer/project_1.srcs/sources_1/new/*.sv]
read_verilog -sv [glob dut/*.sv]

set_property -name "top" -value "tb_act3" -objects [get_filesets sim_1]
set_property -name "xsim.simulate.runtime" -value "1s" -objects [get_filesets sim_1]

update_compile_order -fileset sources_1
launch_simulation
