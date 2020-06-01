`timescale 1ns / 1ps

module tb_alu();
	bit clk = 1'b0;

	always #1 clk = ~clk;

	//

	logic [7:0] A, B, Result, ResultRef;
	logic [3:0] Status, StatusRef;
	logic [1:0] OpCode;
	bit error = 1'b0;
	bit pass = 1'b1;

	initial begin
		{A, B, OpCode} = '0;

		while(1) begin
			@(posedge clk);

			error = ({Result, Status} !== {ResultRef, StatusRef});

			if(error) begin
				$error($sformatf("A: %02X | B: %02X | Op: %d | Output is %02X (status %04b), but expected %02X (status %04b)", A, B, OpCode, Result, Status, ResultRef, StatusRef));
				pass = 1'b0;
			end

			if(&{A, B, OpCode}) begin
				$display("------------------");

				if(pass) begin
					$display("       PASS       ");
				end else begin
					$display("       FAIL       ");
				end

				$display("------------------");
				$finish;
			end

			{A, B, OpCode} += 'd1;
		end
	end

	//

	S4_Actividad3 #(8) DUT
	(
		.A(A),
		.B(B),

		.OpCode(OpCode),

		.Result(Result),
		.Status(Status)
	);

	tb_alu_ref #(8) REF
	(
		.A(A),
		.B(B),

		.OpCode(OpCode),

		.Result(ResultRef),
		.Status(StatusRef)
	);
endmodule
