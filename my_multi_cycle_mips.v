
`timescale 1ns/100ps

   `define ADD  4'b0000
   `define SUB  4'b0001
   `define SLT  4'b0010
   `define SLTU 4'b0011
   `define AND  4'b0100
   `define XOR  4'b0101
   `define OR   4'b0110
   `define NOR  4'b0111
   `define LUI  4'h8

module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR;
   reg [31:0] hi=32'h00000000;
   reg [31:0] lo=32'h00000000; //hi and low start with zero
   reg [31:0] MemtoRegMux,MAR_Mux;
   reg [31:0] PC_input, RegDstMux;
   


   // Data Path Control Lines, donot forget, regs are not always regs !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt;
   reg hi_WE,lo_WE;
   reg multu_start;

   // Memory Ports Binding
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Lines
   reg [3:0] aluOp;
   reg [1:0] aluSelB;
   reg SgnExt, aluSelA;//,  IorD
   reg [1:0] RegDst,IorD_or_JPC_or_JRPC;
   reg [2:0]  MemtoReg;
   reg [1:0] PCMux;
   //reg hi_or_lo;
   reg multu_start_clear, multu_start_set;
   

   // Wiring
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2;
   wire [63:0] multu_Prod;
   wire multu_ready;

    
   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt )
         PC <= #0.1 PC_input;//formerly aluresult

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 MAR_Mux;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;


      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;
      if (lo_WE) lo <= #0.1 multu_Prod[31:0];
      if (hi_WE) hi <= #0.1 multu_Prod[63:32];
      if (multu_start_set) multu_start <= #0.1 1'b1; 
      if (multu_start_clear) multu_start <= #0.1 1'b0; 

   end

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      .WR( RegDstMux ),///change for jal and jalr        RegDst ? IR[15:11] : IR[20:16]
      .WD( MemtoRegMux )
   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};// SgnExt 1 sign extend, 0 zero extend

   //jump PC
   wire [31:0] jPC = {PC[31:28],IR[25:0],2'b00};

   // ALU-A Mux
   wire [31:0] aluA = aluSelA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*) begin
        case (aluSelB)
        2'b00: aluB = B;
        2'b01: aluB = 32'h4;
        2'b10: aluB = SZout;
        2'b11: aluB = SZout << 2;
        endcase
   end
   //Memtoreg Mux
   always @(*) begin
       case (MemtoReg)
            3'b000: MemtoRegMux=aluResult;
            3'b001: MemtoRegMux=MDR;
            3'b010: MemtoRegMux=hi;
            3'b011: MemtoRegMux=lo;
            3'b100: MemtoRegMux=PC;
        endcase
   end

   //PC mux
   always @(*) begin
       case(PCMux) 
            2'b00: PC_input=aluResult;
            2'b01: PC_input=jPC;
            2'b10: PC_input=A;//maybe RD1 but not important really
       endcase
   end

   //RegDst Mux
   always @(*) begin
       case(RegDst) 
            2'b00: RegDstMux=IR[20:16];
            2'b01: RegDstMux=IR[15:11];
            2'b10: RegDstMux=31;//maybe RD1 but not important really
       endcase
   end   

   always @(*) begin
      case(IorD_or_JPC_or_JRPC)
         2'b00: MAR_Mux=PC;//old IorD=0
         2'b01: MAR_Mux=aluResult;//old IorD=1
         2'b10: MAR_Mux=jPC;
         2'b11: MAR_Mux=A;
      endcase
   end

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),

      .X( aluResult ),
      .Z( aluZero )
   );
   unsigned_multiplier u_mult(
       .A(A),
       .B(B),
       .clk(clk),
       .start(multu_start),
       .Product(multu_Prod),
       .ready(multu_ready)
   );

   //assign ifBranch= ( MyBeq && aluZero )||( MyBne && (!aluZero) );


   // Controller Starts Here

   // Controller State Registers
   reg [4:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4, EX_JR=5, EX_JALR=6,
      EX_ALU_R = 7, EX_ALU_I = 8, EX_MFLO = 9, EX_MFHI=10,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15, EX_MULTU_1 = 16, EX_MULTU_2 = 17, EX_J=18, EX_JAL=19,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23, EX_BNE_1 = 24,
      EX_BRA_1 = 25, EX_BRA_2 = 26;

   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD_or_JPC_or_JRPC = 2'b00;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD_or_JPC_or_JRPC = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;
      PCMux=2'b00;//default unless changed.

      PCwrt = 0;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;
      lo_WE=0; hi_WE=0;
      multu_start_clear=0;
      multu_start_set=0;

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 2'b01;
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b000: ;
                     3'b001: begin
                                 case (IR[2:0])
                                       3'b000: nxt_state=EX_JR;
                                       3'b001: nxt_state=EX_JALR; 
                                 endcase
                             end
                     3'b010: begin
                                if (IR[2:0]==0) 
                                    nxt_state=EX_MFHI;
                                else if (IR[2:0]==3'b010)
                                    nxt_state=EX_MFLO; 
                             end
                     3'b011: if (IR[2:0]==001) begin 
                                multu_start_set=1;              
                                nxt_state=EX_MULTU_1; 
                            end
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;

                     3'b110: ;
                     3'b111: ;
                  endcase
               6'b000010: nxt_state=EX_J;
               6'b000011: nxt_state=EX_JAL;
               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110,             // xori
               6'b001_111:             // lui
                  nxt_state = EX_ALU_I;

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100:  nxt_state = EX_BRA_1; 
               6'b000_101:
                            nxt_state = EX_BNE_1; 
                  
                  

               // rest of instructiones should be decoded here

            endcase
         end

         EX_ALU_R: begin
                aluSelA=1'b1;
                aluSelB=2'b00;
                RegDst=2'b01;
                MemtoReg=3'b000;
                RFwrt=1;
                case (IR[3:0])
                    4'b0000: aluOp=`ADD;
                    4'b0001: aluOp=`ADD;//addu in fact
                    4'b0010: aluOp=`SUB;
                    4'b0011: aluOp=`SUB;//
                    4'b0100: aluOp=`AND;
                    4'b0101: aluOp=`OR;
                    4'b0110: aluOp=`XOR;
                    4'b0111: aluOp=`NOR;
                    4'b1010: aluOp=`SLT;
                    4'b1011: aluOp=`SLTU;
                endcase
                PrepareFetch;
         end

         EX_ALU_I: begin
                aluSelA=1'b1;
                aluSelB=2'b10;
                RegDst=2'b00;
                MemtoReg=3'b000;
                RFwrt=1;
                case (IR[31:26])
                    6'b001000: begin  aluOp=`ADD; SgnExt=1; end
                    6'b001001: begin  aluOp=`ADD; SgnExt=1; end//addu in fact
                    6'b001010: begin  aluOp=`SLT; SgnExt=1; end
                    6'b001011: begin aluOp=`SLTU; SgnExt=0; end
                    6'b001100: begin  aluOp=`AND; SgnExt=0; end 
                    6'b001101: begin   aluOp=`OR; SgnExt=0; end
                    6'b001110: begin  aluOp=`XOR; SgnExt=0; end 
                    6'b001111: begin  aluOp=`LUI; SgnExt=0; end
                endcase
                PrepareFetch;
         end

         EX_LW_1: begin
            aluOp=`ADD;
            aluSelA=1;
            aluSelB=2'b10;
            SgnExt=1;
            setMRE=1;//starts reading in next clock
            MARwrt=1;
            IorD_or_JPC_or_JRPC=2'b01;//means set MAR
            nxt_state = EX_LW_2;
         end

         EX_LW_2: begin
            nxt_state = EX_LW_3;
         end

         EX_LW_3: begin
            nxt_state = EX_LW_4;
         end

         EX_LW_4: begin
            setMRE=0;//redundant as everything resets at the beginning of the sate machine block
            clrMRE=1;//stops reading in next clock
            MDRwrt=1;
            RegDst=2'b00;
            nxt_state = EX_LW_5;
         end

         EX_LW_5: begin
            MemtoReg=3'b001;
            RegDst=2'b00;
            RFwrt=1;
            PrepareFetch;
         end

         EX_SW_1: begin
            aluOp=`ADD;
            aluSelA=1;
            aluSelB=2'b10;
            SgnExt=1;
            setMWE=1;
            MARwrt=1;
            IorD_or_JPC_or_JRPC=2'b01;
            nxt_state = EX_SW_2;
         end

         EX_SW_2: begin
            setMWE=0;
            clrMWE=1;
            nxt_state = EX_SW_3;
         end

         EX_SW_3: begin
            PrepareFetch;
         end

         EX_BRA_1: begin
             aluOp=`SUB;//or anything else except for ADD
             aluSelA=1;
             aluSelB=2'b00;//A-B
             if (aluZero)
                nxt_state=EX_BRA_2;
             else 
                PrepareFetch;

         end

         EX_BNE_1: begin
             aluOp=`SUB;//or anything else except for ADD
             aluSelA=1;
             aluSelB=2'b00;//A-B
             if (!aluZero)
                nxt_state=EX_BRA_2;
             else 
                PrepareFetch;

         end
         EX_BRA_2: begin
            aluOp=`ADD;
            aluSelA=0;
            aluSelB=2'b11;
            MARwrt=1;
            setMRE=1;
            PCwrt=1;
            SgnExt=1;
            IorD_or_JPC_or_JRPC=2'b01;//important. PC and MAR independently become the branch PC with (correct) IorD=1
            nxt_state=FETCH1;
         end
         EX_MULTU_1: begin
             multu_start_clear=1;
             nxt_state=EX_MULTU_2;
         end
         EX_MULTU_2: begin
             if (!multu_ready)
                nxt_state=EX_MULTU_2;
             else begin
                 lo_WE=1;
                 hi_WE=1;
                 PrepareFetch;
              end
         end

         EX_MFHI: begin
            RegDst=2'b01;
            MemtoReg=3'b010;
            RFwrt=1; 
            PrepareFetch;
         end
         EX_MFLO: begin
            RegDst=2'b01;
            MemtoReg=3'b011;
            RFwrt=1; 
            PrepareFetch;
         end

         EX_JAL: begin
            RegDst=2'b10;
            MemtoReg=3'b100;
            RFwrt=1;
            IorD_or_JPC_or_JRPC=2'b10;
            PCMux=2'b01;//jPC is the sorce
            MARwrt=1;
            PCwrt=1;
            setMRE=1;
            nxt_state=FETCH1;
         end

         EX_J: begin
            PCMux=2'b01;
            PCwrt=1;
            MARwrt=1;
            IorD_or_JPC_or_JRPC=2'b10;
            setMRE=1;
            nxt_state=FETCH1;
         end

         EX_JR: begin
            PCMux=2'b10;
            PCwrt=1;
            MARwrt=1;
            IorD_or_JPC_or_JRPC=2'b11;
            setMRE=1;
            nxt_state=FETCH1;
         end

         EX_JALR: begin
            RegDst=2'b10;
            MemtoReg=3'b100;
            RFwrt=1;
            IorD_or_JPC_or_JRPC=2'b11;
            PCMux=2'b10;//A is the sorce
            MARwrt=1;
            PCwrt=1;
            setMRE=1;
            nxt_state=FETCH1;
         end
      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input [3:0] Op,
   input [31:0] A,
   input [31:0] B,

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
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         `LUI : x = {B[15:0], 16'h0};
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//==============================================================================

module unsigned_multiplier (
//-----------------------Port directions and deceleration
   input clk,  
   input start,
   input [31:0] A, 
   input [31:0] B, 
   output reg [63:0] Product,
   output ready
    );



//------------------------------------------------------

//----------------------------------- register deceleration
reg [31:0] Multiplicand ;
reg [5:0]  counter;
reg [32:0] adder;
//-------------------------------------------------------

//------------------------------------- wire deceleration
wire product_write_enable;
wire [31:0] adder_output;
wire cout;
//---------------------------------------------------------

//-------------------------------------- combinational logic
//assign adder_output = Product[15:8] + product_write_enable? Multiplicand: 8'h00;
assign product_write_enable = Product[0];
assign ready = counter[5];
assign cout=adder[32];
assign adder_output=adder[31:0];

always @(Product) begin
    if (product_write_enable)
        adder = Product[63:32] + Multiplicand;
    else
        adder = Product[63:32] + 0 ;
end
//---------------------------------------------------------

//--------------------------------------- sequential Logic
always @ (posedge clk)

   if(start) begin
      counter <= 0 ;
      Product <= {32'h00000000, B};
      Multiplicand <= A;
   end

   else if(! ready) begin
         counter <= counter + 1;
         Product[63] <= cout;
         Product[62:31] <= adder_output;
         Product[30:0] <= Product[31:1];
   end   

endmodule