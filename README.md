# verilog-projects
Basic RTL designs
`timescale 1ns / 1ps

// ===============================================================
// ==================== PIPELINED MIPS 32 ========================
// ===============================================================

module pipe_MIPS32 (
    input clk1, 
    input clk2,
    output reg [31:0] Reg1_out,   // R1 (Principal)
    output reg [31:0] Reg8_out,  // R8 (Simple Interest)
output reg [31:0] Reg11_out     // R11 (Power)
);

// Internal Registers and Memory
reg [31:0] PC, IF_ID_IR, IF_ID_NPC;
reg [31:0] ID_EX_IR, ID_EX_NPC, ID_EX_A, ID_EX_B, ID_EX_Imm;
reg [2:0]  ID_EX_type, EX_MEM_type, MEM_WB_type;
reg [31:0] EX_MEM_IR, EX_MEM_ALUOut, EX_MEM_B;
reg        EX_MEM_cond;
reg [31:0] MEM_WB_IR, MEM_WB_ALUOut, MEM_WB_LMD;
reg [31:0] Reg [0:31];     // Register file
reg [31:0] Mem [0:49];     // Memory
integer i;

// Opcodes
parameter ADD   = 6'b000000,
          SUB   = 6'b000001,
          AND   = 6'b000010,
          OR    = 6'b000011,
          SLT   = 6'b000100,
          MUL   = 6'b000101,
          HLT   = 6'b111111,
          LW    = 6'b001000,
          SW    = 6'b001001,
          ADDI  = 6'b001010,
          SUBI  = 6'b001011,
          SLTI  = 6'b001100,
          BNEQZ = 6'b001101,
          BEQZ  = 6'b001110,
          BEQ   = 6'b001111;

// Instruction types
parameter RR_ALU = 3'b000,
          RM_ALU = 3'b001,
          LOAD   = 3'b010,
          STORE  = 3'b011,
          BRANCH = 3'b100,
          HALT   = 3'b101;

reg HALTED;
reg TAKEN_BRANCH;

// Initialize memory and registers
initial begin
    PC = 0;  
    HALTED = 0;
    TAKEN_BRANCH = 0;
    
    // Initialize registers
    for (i = 0; i < 32; i = i + 1)
        Reg[i] = 32'd0;
    
    // Initialize memory
    for (i = 0; i < 50; i = i + 1)
        Mem[i] = 32'd0;
    
    // ======== PROGRAM LOADED INTO MEMORY ========
    // PRINCIPLE
    Mem[0] = 32'b001010_00000_00001_0000001111101000;  // ADDI R1,R0,1000

    Mem[1] = 32'h0ce73800;  // dummy
    Mem[2] = 32'b001010_00000_00010_0000000000000001;  // ADDI R2,R0,1 -- TIME
    Mem[3] = 32'h0ce73800;  // dummy

    Mem[4] = 32'b001010_00000_00011_0000000000001010;  // ADDI R3,R0,10 -- RATE
    Mem[5] = 32'h0ce73800;  // dummy

    Mem[6] = 32'b001010_00000_00100_0000000001100100;  // ADDI R4,R0,100
    Mem[7] = 32'h0ce73800;  // dummy

    Mem[8] = 32'h0ce73800;  // dummy
    Mem[9] = 32'b000101_00001_00010_00101_00000_000000;  // MUL R5,R1,R2

    // 2nd step: MUL R6,R5,R3
    Mem[12] = 32'b000101_00101_00011_00110_00000_000000;

    // DIV step (using opcode 000110 as DIV, though not defined in params)
    Mem[15] = 32'b000110_00110_00100_01000_00000_000000;  // DIV R8,R6,R4

    // POWER
    Mem[18] = 32'b001010_00000_01001_0000000000001001;  // ADDI R9,R0,9  
    Mem[19] = 32'h0ce73800;  // dummy
    Mem[20] = 32'b001010_00000_01010_0000000000000010;  // ADDI R10,R0,2
    Mem[21] = 32'h0ce73800;  // dummy
    Mem[22] = 32'b000111_01001_01010_01011_00000_000000;  // POW R11,R9**R10
    Mem[23] = 32'h0ce73800;  // dummy
    Mem[24] = 32'h0ce73800;  // dummy

    // PERCENTAGE
    Mem[25] = 32'b001010_00000_01100_0000001111101000;  // ADDI R12,R0,1000
    Mem[26] = 32'h0ce73800;  // dummy
    Mem[27] = 32'h0ce73800;  // dummy
    Mem[28] = 32'b001010_00000_01101_0000000000010100;  // ADDI R13,R0,20
    Mem[29] = 32'h0ce73800;  // dummy
    Mem[30] = 32'h0ce73800;  // dummy
    Mem[31] = 32'b000110_01100_00100_01110_00000_000000;  // DIV R14,R12,R4
    Mem[32] = 32'h0ce73800;  // dummy
    Mem[33] = 32'h0ce73800;  // dummy
    Mem[34] = 32'b000101_01110_01101_01111_00000_000000;  // MUL R15,R14,R13
end

// ==================== IF Stage ====================
always @(posedge clk1) begin
    if (!HALTED) begin
        if (((EX_MEM_IR[31:26] == BEQZ)  && (EX_MEM_cond == 1'b1)) || 
            ((EX_MEM_IR[31:26] == BNEQZ) && (EX_MEM_cond == 1'b0)) ||
            ((EX_MEM_IR[31:26] == BEQ)   && (EX_MEM_cond == 1'b1))) begin
            
            IF_ID_IR  <= Mem[EX_MEM_ALUOut];
            TAKEN_BRANCH <= 1'b1;
            IF_ID_NPC <= EX_MEM_ALUOut + 1;
            PC        <= EX_MEM_ALUOut + 1;

        end else begin
            IF_ID_IR  <= Mem[PC];
            IF_ID_NPC <= PC + 1;
            PC        <= PC + 1;
            TAKEN_BRANCH <= 1'b0;
        end
    end
end

// ==================== ID Stage ====================
always @(posedge clk2) begin
    if (!HALTED) begin
        ID_EX_A   <= (IF_ID_IR[25:21] == 5'b00000) ? 32'b0 : Reg[IF_ID_IR[25:21]];
        ID_EX_B   <= (IF_ID_IR[20:16] == 5'b00000) ? 32'b0 : Reg[IF_ID_IR[20:16]];
        ID_EX_NPC <= IF_ID_NPC;
        ID_EX_IR  <= IF_ID_IR;
        ID_EX_Imm <= {{16{IF_ID_IR[15]}}, IF_ID_IR[15:0]};

        case (IF_ID_IR[31:26])
            ADD, SUB, AND, OR, SLT, MUL: ID_EX_type <= RR_ALU;
            ADDI, SUBI, SLTI:            ID_EX_type <= RM_ALU;
            LW:                          ID_EX_type <= LOAD;
            SW:                          ID_EX_type <= STORE;
            BNEQZ, BEQZ, BEQ:            ID_EX_type <= BRANCH;
            HLT:                         ID_EX_type <= HALT;
            default:                     ID_EX_type <= HALT;
        endcase
    end
end

// ==================== EX Stage ====================
always @(posedge clk1) begin
    if (!HALTED) begin
        EX_MEM_type <= ID_EX_type;
        EX_MEM_IR   <= ID_EX_IR;

        case (ID_EX_type)
            RR_ALU: begin
                case (ID_EX_IR[31:26])
                    ADD: EX_MEM_ALUOut <= ID_EX_A + ID_EX_B;
                    SUB: EX_MEM_ALUOut <= ID_EX_A - ID_EX_B;
                    AND: EX_MEM_ALUOut <= ID_EX_A & ID_EX_B;
                    OR:  EX_MEM_ALUOut <= ID_EX_A | ID_EX_B;
                    SLT: EX_MEM_ALUOut <= (ID_EX_A < ID_EX_B) ? 32'd1 : 32'd0;
                    MUL: EX_MEM_ALUOut <= ID_EX_A * ID_EX_B;
                    default: EX_MEM_ALUOut <= 32'h00000000;
                endcase
            end
            
            RM_ALU: begin
                case (ID_EX_IR[31:26])
                    ADDI: EX_MEM_ALUOut <= ID_EX_A + ID_EX_Imm;
                    SUBI: EX_MEM_ALUOut <= ID_EX_A - ID_EX_Imm;
                    SLTI: EX_MEM_ALUOut <= (ID_EX_A < ID_EX_Imm) ? 32'd1 : 32'd0;
                    default: EX_MEM_ALUOut <= 32'h00000000;
                endcase
            end
            
            LOAD, STORE: begin
                EX_MEM_ALUOut <= ID_EX_A + ID_EX_Imm;
                EX_MEM_B      <= ID_EX_B;
            end
            
            BRANCH: begin
                EX_MEM_ALUOut <= ID_EX_NPC + ID_EX_Imm;
                case (ID_EX_IR[31:26])
                    BEQZ:  EX_MEM_cond <= (ID_EX_A == 32'b0);
                    BNEQZ: EX_MEM_cond <= (ID_EX_A != 32'b0);
                    BEQ:   EX_MEM_cond <= (ID_EX_A == ID_EX_B);
                    default: EX_MEM_cond <= 1'b0;
                endcase
            end
        endcase
    end
end

// ==================== MEM Stage ====================
always @(posedge clk2) begin
    if (!HALTED) begin
        MEM_WB_type <= EX_MEM_type;
        MEM_WB_IR   <= EX_MEM_IR;

        case (EX_MEM_type)
            RR_ALU, RM_ALU: MEM_WB_ALUOut <= EX_MEM_ALUOut;
            LOAD:           MEM_WB_LMD    <= Mem[EX_MEM_ALUOut];
            STORE: begin
                if (TAKEN_BRANCH == 1'b0) begin
                    Mem[EX_MEM_ALUOut] <= EX_MEM_B;
                end
            end
        endcase
    end
end

// ==================== WB Stage ====================
always @(posedge clk1) begin
    if (TAKEN_BRANCH == 1'b0) begin
        case (MEM_WB_type)
            RR_ALU: Reg[ MEM_WB_IR[15:11] ] <= MEM_WB_ALUOut;
            RM_ALU: Reg[ MEM_WB_IR[20:16] ] <= MEM_WB_ALUOut;
            LOAD:   Reg[ MEM_WB_IR[20:16] ] <= MEM_WB_LMD;
            HALT:   HALTED <= 1'b1;
        endcase
        
        // Update output registers
        Reg1_out <= Reg[1];  // Principal
        Reg8_out <= Reg[8];  // Simple Interest
        Reg11_out <= Reg[11];  // Power result
    end
end

endmodule


// ===============================================================
// ==================== top_mips_system ==========================
// ===============================================================

module top_mips_system (
    input clk,
    input reset,
    output [31:0] Reg1_out,
    output [31:0] Reg8_out,
    output [31:0] Reg11_out
);

    wire slow_clk;
    wire clk1, clk2;

    clock_divider #(.DIVIDE_BY(500000)) slow_clk_gen (
        .clk_in(clk),
        .reset(reset),
        .clk_out(slow_clk)
    );

    clk_sequencer clock_gen (
        .clk(slow_clk),
        .reset(reset),
        .clk1(clk1),
        .clk2(clk2)
    );

    pipe_MIPS32 mips_processor (
        .clk1(clk1),
        .clk2(clk2),
        .Reg1_out(Reg1_out),
        .Reg8_out(Reg8_out),.Reg11_out(Reg11_out)
    );

endmodule


// ===============================================================
// ==================== CLOCK DIVIDER ============================
// ===============================================================

module clock_divider #( parameter DIVIDE_BY = 100 )(
    input clk_in,
    input reset,
    output reg clk_out
);

reg [31:0] counter;

always @(posedge clk_in or posedge reset) begin
    if (reset) begin
        counter <= 0;
        clk_out <= 0;
    end else begin
        if (counter == (DIVIDE_BY/2 - 1)) begin
            clk_out <= ~clk_out;
            counter <= 0;
        end else begin
            counter <= counter + 1;
        end
    end
end

endmodule


// ===============================================================
// ==================== CLOCK SEQUENCER ==========================
// ===============================================================

module clk_sequencer (
    input clk,
    input reset,
    output reg clk1,
    output reg clk2
);

reg [1:0] state;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        clk1 <= 0;
        clk2 <= 0;
        state <= 0;
    end else begin
        case (state)
            0: begin clk1 <= 1; clk2 <= 0; state <= 1; end
            1: begin clk1 <= 0; clk2 <= 1; state <= 2; end
            2: begin clk1 <= 0; clk2 <= 0; state <= 0; end
            default: state <= 0;
        endcase
    end
end

endmodule


// ===============================================================
// ====================== FPGA TOP WRAPPER =======================
// ===============================================================

module fpga_top (
    input clk,          // FPGA board clock
    input reset,        // Reset push-button
    output [7:0] leds   // FPGA board LEDs
);

    wire [31:0] reg1_val;
    wire [31:0] reg8_val;
    wire [31:0] reg11_val;

top_mips_system U1 (
    .clk(clk),
    .reset(reset),
    .Reg1_out(reg1_val),
    .Reg8_out(reg8_val),
    .Reg11_out(reg11_val)
);

// Show POWER RESULT (R11)
assign leds = reg11_val[7:0];

// If active-low LEDs:
// assign leds = ~reg11_val[7:0];
endmodule
