`timescale 1ns / 1ps

module tb_act1();
	localparam C_DEBOUNCER_DELAY = 10;
	localparam C_NUM_TESTS = 5000;

	bit pass = 1'b1;

	// clk generation

	bit clk = 1'b0;
	always #1 clk = ~clk;

	// input generation

	bit rst_n = 1'b0;
	logic in_enter = 1'b0;
	logic [15:0] in_number = 16'd0;

	task button_press(input int length);
		in_number = $urandom;

		for(int i = $urandom_range(1, 5)*2; i != 0; --i) begin
			in_enter = ~in_enter;

			for(int j = $urandom_range(1, C_DEBOUNCER_DELAY/2); j != 0; --j) begin
				#2;
			end
		end

		in_enter = 1'b1;

		for(int i = 0; i < length; ++i) begin
			#2;

			if(i > C_DEBOUNCER_DELAY + 2) begin
				in_number = $urandom;
			end
		end

		in_enter = 1'b0;

		for(int i = 0; i < 4; ++i) begin
			#40 in_number = $urandom;
		end
	endtask

	initial begin
		#2
		rst_n = 1'b1;
		#50;

		for(int i = 0; i < 3*(C_NUM_TESTS/2); ++i) begin
			button_press($urandom_range(C_DEBOUNCER_DELAY + 1, 100));
		end

		rst_n = 1'b0;
		#50
		rst_n = 1'b1;
		#50;

		for(int i = 0; i < 3*(C_NUM_TESTS/2); ++i) begin
			button_press($urandom_range(C_DEBOUNCER_DELAY + 1, 100));
		end

		$display("------------------");

		if(pass) begin
			$display("       PASS       ");
		end else begin
			$display("       FAIL       ");
		end

		$display("------------------");
		$finish;
	end

	// validate outputs

	logic [3:0] out_flags, ref_flags;
	logic [15:0] out_display, ref_display;
	int out_state;

	assert property (
		@(posedge clk) disable iff (~rst_n | ~pass)
			~$stable(ref_display) & ~in_enter |-> ##4 (ref_display == out_display) [*1:$]
	)
	else begin
		pass = 0;
		$error("incorrect value in display");
	end

	assert property (
		@(posedge clk) disable iff (~rst_n | ~pass)
			~$stable(ref_flags) & ~in_enter |-> ##4 (ref_flags == out_flags) [*1:$]
	)
	else begin
		pass = 0;
		$error("incorrect flags value");
	end

	// Tested module

	Act1_RPCalculator
	#(
		.N_debouncer(C_DEBOUNCER_DELAY)
	)
	DUT
	(
		.clk(clk),
		.resetN(rst_n),
		.Enter(in_enter),
		.DataIn(in_number),
		.Flags(out_flags),
		.ToDisplay(out_display),
		.CurrentState(out_state)
	);

	// Reference

	calc_fsm
	#(
		.C_DEBOUNCER_DELAY(C_DEBOUNCER_DELAY)
	)
	REF
	(
		.clk(clk),
		.rst_n(rst_n),

		.enter(in_enter),
		.undo(1'b0),

		.value(in_number),

		.display(ref_display),
		.flags(ref_flags)
	);
endmodule
