#![doc = include_str!("../README.md")]
#![forbid(future_incompatible)]
#![warn(missing_docs, missing_debug_implementations, bare_trait_objects)]

pub mod error;
pub mod opcode;
pub mod operand;

use std::io::Read;
pub use crate::{
    error::{Error, Result},
    opcode::{
        AccessType,
        DataType,
        DataValue,
        ReadDataValue,
        WriteDataValue,
        Instruction,
        Opcode,
    },
    operand::{IndexedOperand, Operand, ReadOperand, Register},
};

/// Extends [`Read`] with a method to read a VAX operand ([`Operand`]).
///
/// # Examples
///
/// ```rust
/// use vax_disassembler::ReadMacro32;
/// use std::io::Cursor;
///
/// macro_rules! disassemble {
///     ($buf: expr, $text: expr) => {
///         let instruction = Cursor::new($buf).disassemble().unwrap();
///         assert_eq!(&format!("{}", instruction), $text);
///     };
/// }
///
/// disassemble!([0x05], "RSB");
/// disassemble!([0xE9, 0x50, 0x15], "BLBC    R0, 21");
/// disassemble!([0xDE, 0x44, 0xC4, 0x00, 0xFE, 0x55], "MOVAL   W^-512(R4)[R4], R5");
/// disassemble!([0xCB, 0x8F, 0xFF, 0xFF, 0xFF, 0x00, 0x50, 0x53], "BICL3   #16777215, R0, R3");
/// disassemble!([0x28, 0x8F, 0x00, 0x02, 0x61, 0xC1, 0x00, 0xFE], "MOVC3   #512, (R1), W^-512(R1)");
/// ```
pub trait ReadMacro32: Read {
    /// Read VAX MACRO32 machine code from a reader and disassemble it into a single
    /// [`Instruction`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use vax_disassembler::ReadMacro32;
    /// use std::io::Cursor;
    ///
    /// macro_rules! disassemble {
    ///     ($buf: expr, $text: expr) => {
    ///         let instruction = Cursor::new($buf).disassemble().unwrap();
    ///         assert_eq!(&format!("{}", instruction), $text);
    ///     };
    /// }
    ///
    /// disassemble!([0x01], "NOP");
    /// disassemble!([0x30, 0x00, 0xFE], "BSBW    -512");
    /// disassemble!([0xDE, 0x44, 0x64, 0x55], "MOVAL   (R4)[R4], R5");
    /// disassemble!([0xEF, 0x0C, 0x14, 0x56, 0x57], "EXTZV   S^#12, S^#20, R6, R7");
    /// disassemble!([0x2C, 0x50, 0x61, 0x20, 0x52, 0x63], "MOVC5   R0, (R1), S^#32, R2, (R3)");
    /// ```
    fn disassemble(&mut self) -> Result<Instruction> {
        let mut buf = [0; 2];
        self.read_exact(&mut buf[0..1])?;
        let opcode = match buf[0] {
            0xFD..=0xFF => {
                self.read_exact(&mut buf[1..2])?;
                let opcode = u16::from_le_bytes(buf);
                Opcode::try_from(opcode)?
            }
            opcode => Opcode::try_from(opcode as u16)?,
        };
        let mut instruction = Instruction::from(opcode);
        let operands = instruction.operands_mut();
        for (index, (access, size)) in opcode.operand_specs().iter().enumerate() {
            operands[index] = self.read_operand(*access, *size)?;
        }
        Ok(instruction)
    }
}

/// All types that implement `Read` get methods defined in `ReadMacro32` for free.
impl<R: Read + ?Sized> ReadMacro32 for R {}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_disassembly {
        ($input: expr, $output: expr) => {
            let mut reader = std::io::Cursor::new($input);
            let output = reader.disassemble().unwrap();
            assert_eq!(&format!("{}", output), $output);
        }
    }

    #[test]
    fn simple_tests() {
        test_disassembly!([0x00], "HALT");
        test_disassembly!([0x01], "NOP");
        test_disassembly!([0x02], "REI");
        test_disassembly!([0x03], "BPT");
        test_disassembly!([0x05], "RSB");
        test_disassembly!([0x10, 20], "BSBB    20");
        test_disassembly!([0x11, 128], "BRB     -128");
    }
}
