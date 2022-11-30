//===========================================================
//
//			Name & Student ID
//
//			Implemented Instructions are:
//			R format:  add(u), sub(u), and, or, xor, nor, slt, sltu;
//			I format:  beq, bne, lw, sw, addiu, slti, sltiu, andi, ori, xori, lui.
//
//===========================================================

`timescale 1ns/1ns

   `define ADD  4'h0
   `define SUB  4'h1
   `define SLT  4'h2
   `define SLTU 4'h3
   `define AND  4'h4
   `define OR   4'h5
   `define NOR  4'h6
   `define XOR  4'h7
   `define LUI  4'h8

module single_cycle_mips 
(
	input clk,
	input reset
);
 
	initial begin
		$display("Single Cycle MIPS Implemention");
		$display("Name & Student ID");
	end

	reg [31:0] PC;          // Keep PC as it is, its name is used in higher level test bench

   wire [31:0] instr;
   wire [ 5:0] op   = instr[31:26];
   wire [ 5:0] func = instr[ 5: 0];

   wire [31:0] RD1, RD2, AluResult, MemReadData;

   wire AluZero;

   // Control Signals

   wire PCSrc;
   wire MyBeq,MyBne;//my line

   reg SZEn, ALUSrc, RegDst, MemtoReg, RegWrite, MemWrite,jump;


   reg [3:0] AluOP;

	
	// CONTROLLER COMES HERE

   always @(*) begin
      SZEn = 1'bx;
      AluOP = 4'hx;
      ALUSrc = 1'bx;
      RegDst = 1'bx;
      MemtoReg = 1'bx;
      RegWrite = 1'b0;
      MemWrite = 1'b0;
      jump=0;

      case(op)
        6'b000000: begin//r-format   
                    ALUSrc=0;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=1;
                    MemtoReg=0;
                    MemWrite=0;
                    RegWrite=1;
                    SZEn=1'bx;
                    case(func)
                        6'b100000: AluOP=ADD;//add
                        6'b100001: AluOP=ADD;//addu
                        6'b100010: AluOP=SUB;//sub
                        6'b100011: AluOP=SUBU;//subu
                        6'b100100: AluOP=AND;//and
                        6'b100101: AluOP=OR;//or
                        6'b100110: AluOP=XOR;//xor
                        6'b100111: AluOP=NOR;//nor
                        6'b101000: AluOP=SLT;//slt
                        6'b101001: AluOP=SLTU;//sltu                        
                    end
        6'b001000: begin //addi
                    AluOP=ADD;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=0;
                    MemtoReg=0;
                    MemWrite=0;
                    SZEn=1;
                    RegWrite=1;
                    end
        6'b001001: begin //addiu
                    AluOP=ADD;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=0;
                    MemtoReg=0;
                    MemWrite=0;
                    SZEn=1;
                    RegWrite=1;
                    end                    
        6'b001010: begin //slti
                    AluOP=SLT;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=0;
                    MemtoReg=0;
                    MemWrite=0;
                    SZEn=1;
                    RegWrite=1;
                    end
        6'b001011: begin //sltiu
                    AluOP=SLTU;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=0;
                    MemtoReg=0;
                    MemWrite=0;
                    SZEn=0;
                    RegWrite=1;
                    end
        6'b001100: begin //andi
                    AluOP=AND;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=0;
                    MemtoReg=0;
                    MemWrite=0;
                    SZEn=0;
                    RegWrite=1;
                    end        
        6'b001101: begin //ori
                    AluOP=OR;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=0;
                    MemtoReg=0;
                    MemWrite=0;
                    SZEn=0;
                    RegWrite=1;
                    end      
        6'b001110: begin //xori
                    AluOP=XOR;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=0;
                    MemtoReg=0;
                    MemWrite=0;
                    SZEn=0;
                    RegWrite=1;
                    end      
        6'b001111: begin //lui
                    AluOP=LUI;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=0;
                    MemtoReg=0;
                    MemWrite=0;
                    SZEn=0;
                    RegWrite=1;
                    end 
        6'b000100: begin //beq
                    AluOP=SUB;//or anything else except for ADD
                    ALUSrc=1;
                    MyBeq=1;
                    MyBne=0;
                    RegDst=0;
                    MemtoReg=0;
                    MemWrite=0;
                    SZEn=0;
                    RegWrite=0;
                    end 
        6'b000101: begin //bne
                    AluOP=SUB;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=1;
                    RegDst=0;
                    MemtoReg=0;
                    MemWrite=0;
                    SZEn=0;
                    RegWrite=0;
                    end 
        6'b100011: begin //lw
                    AluOP=ADD;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=0;
                    MemtoReg=1;
                    MemWrite=0;
                    SZEn=1;
                    RegWrite=1;
                    end 
        6'b101011: begin //sw
                    AluOP=ADD;
                    ALUSrc=1;
                    MyBeq=0;
                    MyBne=0;
                    RegDst=1'bx;
                    MemtoReg=1'bx;
                    MemWrite=1;
                    SZEn=1;
                    RegWrite=0;
                    end
        6'b000010: begin //jump
                    jump=1;
                    RegWrite=0;
                    MemWrite=0;
                    MyBeq=1'bx;//datapath ensures branching does not happen
                    MyBne=1'bx;
                    AluOP=4'bx;
                    ALUSrc=1'bx;
                    RegDst=1'bx;
                    MemtoReg=1'bx;
                    SZEn=1'bx;
                    end         
        default: begin end

//      YOU COMPLETE THE REST


   end


	// DATA PATH STARTS HERE
   assign PCSrc= ( MyBeq && AluZero )||( MyBne && (!AluZero) );

   wire [31:0] Imm32 = SZEn ? {{16{instr[15]}},instr[15:0]} : {16'h0, instr[15:0]};     // SZEn: 1 sign extend, 0 zero extend
   wire [31:0] jPC = {PC[31:28],instr[25:0],2'b00};

   wire [31:0] PCplus4 = PC + 4'h4;

   wire [31:0] PCbranch = PCplus4 + Imm32 << 2;

   always @(posedge clk)
      if(reset)
         PC <= 32'h0
      else
         PC <= jump? jPC: 
               PCSrc ? PCbranch : PCplus4;//PCSrc ? PCbranch : PCplus4


//========================================================== 
//	instantiated modules
//========================================================== 

// Register File

// NOTE NOTE NOTE: It's now yet incomplete

   reg_file rf
   (
      .clk   ( clk ),
      .write ( RegWrite ),
      .WR    ( RegDst   ? instr[15:11] : instr[20:16]),
      .WD    ( MemtoReg ? MemReadData  : AluResult),
      .RR1   ( instr[25:21] ),
      .RR2   ( instr[20:16] ),
      .RD1   ( RD1 ),
      .RD2   ( RD2 )
	);

   my_alu alu
   (
      .Op( AluOP ),
      .A ( RD1 ),
      .B ( ALUSrc ? Imm32 : RD2),
      .X ( AluResult ),
      .Z ( AluZero )
   );
   


//	Instruction Memory
	async_mem imem			// keep the exact instance name
	(
		.clk		   (1'b0),
		.write		(1'b0),		// no write for instruction memory
		.address	   ( PC ),		   // address instruction memory with pc
		.write_data	(32'bx),
		.read_data	( instr )
	);
	
// Data Memory
	async_mem dmem			// keep the exact instance name
	(
		.clk		   ( clk ),
		.write		( MemWrite ),
		.address	   ( AluResult ),
		.write_data	( RD2 ),
		.read_data	( MemReadData )
	);

endmodule


//==============================================================================

module my_alu(
   input  [3:0] Op,
   input  [31:0] A,
   input  [31:0] B,
   output [31:0] X,
   output        Z
   );

   wire sub = Op != `ADD;
   wire [31:0] bb = sub ? ~B : B;
   wire [32:0] sum = A + bb + sub;
   wire sltu = ! sum[32];

   wire v = sub ?
            ( A[31] != B[31] && A[31] != sum[31] )
          : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x = A & B;
         `OR  : x = A | B;
         `NOR : x = ~(A | B);
         `XOR : x = A ^ B;
         `LUI : x = {B[15:0], 16'h0};
         default : x = 32'hxxxxxxxx;
      endcase

   assign X = x;
   assign Z = x == 32'h00000000;

endmodule

//============================================================================
