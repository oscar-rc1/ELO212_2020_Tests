cd [file dirname [info script]]

create_project -force Sesion4_ELO212_Test1 -part xc7a100tcsg324-1 vivado/test1

read_verilog -sv tb/tb_display_mux.sv
read_verilog -sv [glob dut/*.sv]

set_property -name "top" -value "tb_display_mux" -objects [get_filesets sim_1]
set_property -name "xsim.simulate.runtime" -value "1s" -objects [get_filesets sim_1]

update_compile_order -fileset sources_1
launch_simulation
