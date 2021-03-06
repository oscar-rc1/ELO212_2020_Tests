`timescale 1ns / 1ps

module tb_act3();
	localparam C_NUM_TESTS = 1000;

	localparam C_DEBOUNCER_DELAY = 10;
	localparam C_MASK_OPCODE_BITS = 0;
	localparam C_BUTTON_EDGE = 0;       // 0 -> pressed,           1 -> released
	localparam C_SWAP_SEGMENTS = 1;     // 0 -> {CA, CB, ..., CG}, 1 -> {CG, ..., CB, CA}

	bit pass = 1'b1;

	// clk generation

	bit clk = 1'b0;
	always #1 clk = ~clk;

	// input generation

	bit rst_n = 1'b0;
	logic in_button = 1'b0, in_enter = 1'b0, in_undo = 1'b0, in_format = 1'b0;
	logic [15:0] in_number = 16'd0;
	logic button_sel = 1'b0;

	task button_press(input int length);
		in_number = $urandom;

		for(int i = $urandom_range(1, 5)*2; i != 0; --i) begin
			in_button = ~in_button;

			for(int j = $urandom_range(1, C_DEBOUNCER_DELAY/2); j != 0; --j) begin
				#2;
			end
		end

		in_button = 1'b1;

		for(int i = 0; i < length; ++i) begin
			#2;
		end

		in_button = 1'b0;

		for(int i = 0; i < 4; ++i) begin
			#600
			in_number = $urandom;
			in_format = $urandom_range(0, 1);
		end
	endtask

	initial begin
		#2
		rst_n = 1'b1;
		#50;

		for(int i = 0; i < 3*(C_NUM_TESTS/2); ++i) begin
			button_sel = ($urandom_range(1, 3) == 3);
			button_press($urandom_range(C_DEBOUNCER_DELAY + 1, 100));
		end

		rst_n = 1'b0;
		#50
		rst_n = 1'b1;
		#50;

		for(int i = 0; i < 3*(C_NUM_TESTS/2); ++i) begin
			button_sel = ($urandom_range(1, 3) == 3);
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

	always_comb begin
		if(~button_sel) begin
			in_enter = in_button;
			in_undo = 1'b0;
		end else begin
			in_enter = 1'b0;
			in_undo = in_button;
		end
	end

	// validate outputs

	logic [3:0] out_flags, ref_flags;
	logic [6:0] out_segments;
	logic [4:0] out_anodes;
	logic [15:0] ref_display;
	logic [31:0] out_display;
	int out_state;

	assert property (
		@(posedge clk) disable iff (~rst_n | ~pass)
			~$stable(ref_display) |-> ##200 (ref_display == out_display[15:0]) [*1:$]
	)
	else begin
		pass = 0;
		$error("incorrect value in display");
	end

	assert property (
		@(posedge clk) disable iff (~rst_n | ~pass)
			~$stable(ref_flags) |-> ##200 (ref_flags == out_flags) [*1:$]
	)
	else begin
		pass = 0;
		$error("incorrect flags value");
	end

	// Tested module

	Act3_RPCalculator
	#(
		.N_debouncer(C_DEBOUNCER_DELAY)
	)
	DUT
	(
		.clk(clk),
		.resetN(rst_n),
		.Enter(in_enter),
		.Undo(in_undo),
		.DisplayFormat(in_format),
		.DataIn(in_number),
		.Flags(out_flags),
		.Segments(out_segments),
		.Anodes(out_anodes),
		.CurrentState(out_state)
	);

	sseg_decoder
	#(
		.C_SWAP_SEGMENTS(C_SWAP_SEGMENTS)
	)
	decoder
	(
		.clk(clk),
		.rst_n(rst_n),

		.dec(in_format),
		.segments(out_segments),
		.anodes({'1, out_anodes}),

		.displayed_num(out_display)
	);

	// Reference

	calc_fsm
	#(
		.C_DEBOUNCER_DELAY(C_DEBOUNCER_DELAY),
		.C_MASK_OPCODE_BITS(C_MASK_OPCODE_BITS),
		.C_BUTTON_EDGE(C_BUTTON_EDGE)
	)
	REF
	(
		.clk(clk),
		.rst_n(rst_n),

		.enter(in_enter),
		.undo(in_undo),

		.value(in_number),

		.display(ref_display),
		.flags(ref_flags)
	);
endmodule
