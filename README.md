# vax-disassembler - DEC VAX one-line disassembler

This crate provides a one-instruction disassembler for the Digital Equipment
Corporation VAX architecture.

The [ReadMacro32] trait adds the disassemble() function to any object that
supports the Read trait. The disassemble function returns an [Instruction] enum.

The [Instruction] enum stores information about the disassembled instruction.

The current version supports disassembly and display of the instruction along
with several ways to inspect the details of the instruction. Its intended
purpose is to decode memory dumps from a simulated VAX, however, I have plans
to increase its functionality as time permits.

* Add ability to output machine code from an Instruction.
* Implement The FromStr trait for the Instruction enum (i.e. add one-line assembly functionality to crate).
* Add awareness of the program counter (PC) to the disassembly instruction.

## Examples

```rust
use vax_disassembler::{
    IndexedOperand,
    Instruction,
    Operand,
    ReadMacro32,
    Register::*,
};
use std::io::Cursor;

static SAMPLE_BUFFER: &'static [u8] = &[
    // PUSHR   #0x3F                        ; Push R0 through R5 on the stack
    0xBB, 0x3F,
    // EDIV    -4(R2)[R3], R0, 16(SP), 20(SP); Divide R0:R1 by longword at (R3 * 4) + R2 - 4.
    //                                      ; Put dividend in SP + 8 and remainder in SP + 12
    0x7B, 0x43, 0xA2, 0xFC, 0x50, 0xAE,   16, 0xAE,   20,
    // ADDL2   S^#16, SP                    ; Release stack space
    0xC0,   16, 0x5E,
    // MOVQ    (SP)+, R0                    ; Put dividend in R0 and remainder in R1 from the stack
    0x7D, 0x8E, 0x50,
    // RSB
    0x05,
];

let mut code_buf = Cursor::new(SAMPLE_BUFFER);

let mut instruction = Vec::new();
for _ in 0..5 {
    instruction.push(code_buf.disassemble().unwrap());
}

// The machine code is transformed into Instructions
assert_eq!(instruction[0], Instruction::PUSHR([Operand::Literal(0x3F)]));
assert_eq!(instruction[1], Instruction::EDIV([
    Operand::Indexed(IndexedOperand::ByteDisplacement(-4, R2), R3),
    Operand::Register(R0),
    Operand::ByteDisplacement(16, SP),
    Operand::ByteDisplacement(20, SP),
]));
assert_eq!(instruction[2], Instruction::ADDL2([Operand::Literal(16), Operand::Register(SP)]));
assert_eq!(instruction[3], Instruction::MOVQ([Operand::AutoIncrement(SP), Operand::Register(R0)]));
assert_eq!(instruction[4], Instruction::RSB([]));

// Instructions have a display implementation. . .
assert_eq!(&format!("{}", instruction[0]), "PUSHR   S^#63");
assert_eq!(&format!("{}", instruction[1]), "EDIV    B^-4(R2)[R3], R0, B^16(SP), B^20(SP)");
assert_eq!(&format!("{}", instruction[2]), "ADDL2   S^#16, SP");
assert_eq!(&format!("{}", instruction[3]), "MOVQ    (SP)+, R0");
assert_eq!(&format!("{}", instruction[4]), "RSB");
```
