cd [file dirname [info script]]

create_project -force Sesion4_ELO212_Test3 -part xc7a100tcsg324-1 vivado/test3

read_verilog -sv tb/tb_alu.sv
read_verilog -sv tb/tb_alu_ref.sv
read_verilog -sv [glob dut/*.sv]

set_property -name "top" -value "tb_alu" -objects [get_filesets sim_1]
set_property -name "xsim.simulate.runtime" -value "1s" -objects [get_filesets sim_1]

update_compile_order -fileset sources_1
launch_simulation
