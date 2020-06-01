cd [file dirname [info script]]

create_project -force Sesion4_ELO212_Test2 -part xc7a100tcsg324-1 vivado/test2

read_verilog -sv tb/tb_clock_div.sv
read_verilog -sv [glob dut/*.sv]

set_property -name "top" -value "tb_clock_div" -objects [get_filesets sim_1]
set_property -name "xsim.simulate.runtime" -value "1s" -objects [get_filesets sim_1]

update_compile_order -fileset sources_1
launch_simulation
