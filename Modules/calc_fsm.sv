module calc_fsm
#(
	parameter C_DEBOUNCER_DELAY = 10
)
(
	input logic clk,
	input logic rst_n,

	input logic enter,
	input logic undo,

	input logic [15:0] value,

	output logic [15:0] display,
	output logic [3:0] flags
);
	enum logic [1:0] {ST_INPUT_A, ST_INPUT_B, ST_INPUT_OPCODE, ST_SHOW_RESULT} state;

	logic [15:0] opA, opB, opRes;
	logic [3:0] opFlags;
	logic [1:0] opCode;

	logic enter_db, undo_db;

	always_ff @(posedge clk) begin
		if(~rst_n) begin
			state <= ST_INPUT_A;
		end else if(enter_db) begin
			state <= state.next;
		end else if(undo_db && state != ST_INPUT_A) begin
			state <= state.prev;
		end
	end

	always_ff @(posedge clk) begin
		if(~rst_n) begin
			opA <= 16'd0;
		end else if(enter_db && state == ST_INPUT_A) begin
			opA <= value;
		end
	end

	always_ff @(posedge clk) begin
		if(~rst_n) begin
			opB <= 16'd0;
		end else if(enter_db && state == ST_INPUT_B) begin
			opB <= value;
		end
	end

	always_ff @(posedge clk) begin
		if(~rst_n) begin
			opCode <= 2'd0;
		end else if(enter_db && state == ST_INPUT_OPCODE) begin
			opCode <= value[1:0];
		end
	end

	always_ff @(posedge clk) begin
		if(~rst_n) begin
			flags <= 4'd0;
		end else if(state == ST_SHOW_RESULT) begin
			flags <= opFlags;
		end
	end

	always_comb begin
		if(state == ST_SHOW_RESULT) begin
			display = opRes;
		end else begin
			display = value;
		end
	end

	// Module instances

	ALU_ref
	#(
		.C_WIDTH(16)
	)
	U0
	(
		.A(opA),
		.B(opB),
		.OpCode(opCode),

		.Result(opRes),
		.Status(opFlags)
	);

	PB_Debouncer_FSM
	#(
		.DELAY(C_DEBOUNCER_DELAY)
	)
	U1
	(
		.clk(clk),
		.rst(~rst_n),
		.PB(enter),
		.PB_pressed_pulse(enter_db)
	);

	PB_Debouncer_FSM
	#(
		.DELAY(C_DEBOUNCER_DELAY)
	)
	U2
	(
		.clk(clk),
		.rst(~rst_n),
		.PB(undo),
		.PB_pressed_pulse(undo_db)
	);
endmodule
