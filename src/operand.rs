//! # MACRO32 Operands

use std::{
    convert::TryFrom,
    fmt::{self, Display, Formatter},
    io::Read,
};
use crate::{
    error::{Error, Result},
    opcode::{AccessType, DataType, DataValue, ReadDataValue},
};

macro_rules! define_registers {
    ($(($reg: ident, $value: expr),)+) => {
        /// # VAX General Registers
        ///
        /// The VAX has 16 registers that are directly accessible by all instructions. There are 12
        /// general purpose registers (`R0`-`R11`), two named regisers that can be used as general
        /// purpose registers (`AP` (argument) and `FP` (frame pointer)), and two special purpose
        /// registers (`SP` (stack pointer) and `PC` (program counter)).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use vax_disassembler::operand::Register;
        ///
        /// // All registers directly map to a u8 value.
        $(
            #[doc = concat!("assert_eq!(Register::", stringify!($reg), " as u8, ", stringify!($value), ");")]
        )+
        ///
        /// // All u8 values map to the register based on the low 4 bits.
        /// for byte in (0_u8..=0xF0).step_by(0x10) {
        $(
            #[doc = concat!("   assert_eq!(Register::", stringify!($reg), ", Register::from(byte + ", stringify!($value), "));")]
        )+
        /// }
        /// ```
        #[repr(u8)]
        #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub enum Register {
            $(
            #[doc = concat!(" # The ", stringify!($reg), " Register")]
            ///
            /// ## Examples
            ///
            /// ```rust
            /// use vax_disassembler::Register;
            ///
            /// for high_nibble in 0_u8..16 {
            #[doc = concat!("    let operand_byte = (high_nibble << 4) + ", stringify!($value), ";")]
            #[doc = concat!("    assert_eq!(Register::", stringify!($reg), ", Register::from(operand_byte));")]
            /// }
            /// ```
            $reg = $value,
            )+
        }

        impl From<u8> for Register {
            /// Converts to this type from the input type.
            ///
            /// The general mode addressing formats (other than literal mode) consists of the
            /// register number in bits 0-3 (the low nibble) and the addressing mode specifier bits
            /// in bits 4-7 (the high nibble). `Register::from(u8)` will take bits 0-3 of the u8
            /// value and return the `Register`.
            ///
            /// The register numbers are as follows:
            ///
            /// ```text
            $(
                #[doc = concat!(stringify!($reg), "\t=\t", stringify!($value))]
            )+
            /// ```
            ///
            /// ```rust
            /// use vax_disassembler::operand::Register;
            ///
            $(
                #[doc = concat!("assert_eq!(Register::", stringify!($reg), ", Register::from(", stringify!($value), "));")]
            )+
            /// // Verify that all values of u8 are covered.
            /// for i in 16..=u8::MAX {
            ///     let _ = Register::from(i);
            /// }
            /// ```
            fn from(value: u8) -> Register {
                match value & 0xF {
                    $(
                    $value => Register::$reg,
                    )+
                    _ => unreachable!()
                }
            }
        }

        impl Display for Register {
            /// Formats the value using the given formatter.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::operand::Register;
            ///
            $(
            #[doc = concat!("assert_eq!(&format!(\"{}\", Register::", stringify!($reg), "), \"",
                stringify!($reg), "\");")]
            )+
            /// ```
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                let text = match self {
                    $(
                    Register::$reg => stringify!($reg),
                    )+
                };
                f.write_str(text)
            }
        }
    };
}

define_registers! {
    (R0, 0),
    (R1, 1),
    (R2, 2),
    (R3, 3),
    (R4, 4),
    (R5, 5),
    (R6, 6),
    (R7, 7),
    (R8, 8),
    (R9, 9),
    (R10, 10),
    (R11, 11),
    (AP, 12),
    (FP, 13),
    (SP, 14),
    (PC, 15),
}

/// # VAX Operand Type
///
/// The operand type is the translation from the first byte to determine the addressing mode of the
/// operand.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OperandType {
    #[doc = include_str!("doc/literal.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::OperandType;
    /// for literal in 0_u8..=63 {
    ///     assert_eq!(OperandType::Literal(literal), OperandType::from(literal));
    /// }
    /// ```
    Literal(u8),
    #[doc = include_str!("doc/indexed.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for indexed in 0x40_u8..=0x4E {
    ///     let reg = Register::from(indexed);
    ///     assert_eq!(OperandType::Indexed(reg), OperandType::from(indexed));
    /// }
    /// ```
    Indexed(Register),
    #[doc = include_str!("doc/register.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for register in 0x50_u8..=0x5E {
    ///     let reg = Register::from(register);
    ///     assert_eq!(OperandType::Register(reg), OperandType::from(register));
    /// }
    /// ```
    Register(Register),
    #[doc = include_str!("doc/register_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for register_deferred in 0x60_u8..=0x6E {
    ///     let reg = Register::from(register_deferred);
    ///     assert_eq!(OperandType::RegisterDeferred(reg), OperandType::from(register_deferred));
    /// }
    /// ```
    RegisterDeferred(Register),
    #[doc = include_str!("doc/autodecrement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for autodecrement in 0x70_u8..=0x7E {
    ///     let reg = Register::from(autodecrement);
    ///     assert_eq!(OperandType::AutoDecrement(reg), OperandType::from(autodecrement));
    /// }
    /// ```
    AutoDecrement(Register),
    #[doc = include_str!("doc/autoincrement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for autoincrement in 0x80_u8..=0x8E {
    ///     let reg = Register::from(autoincrement);
    ///     assert_eq!(OperandType::AutoIncrement(reg), OperandType::from(autoincrement));
    /// }
    /// ```
    AutoIncrement(Register),
    #[doc = include_str!("doc/autoincrement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for autoincrement_deferred in 0x90_u8..=0x9E {
    ///     let reg = Register::from(autoincrement_deferred);
    ///     assert_eq!(OperandType::AutoIncrementDeferred(reg),
    ///         OperandType::from(autoincrement_deferred));
    /// }
    /// ```
    AutoIncrementDeferred(Register),
    #[doc = include_str!("doc/byte_displacement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for byte_displacement in 0xA0_u8..=0xAF {
    ///     let reg = Register::from(byte_displacement);
    ///     assert_eq!(OperandType::ByteDisplacement(reg), OperandType::from(byte_displacement));
    /// }
    /// ```
    ByteDisplacement(Register),
    #[doc = include_str!("doc/byte_displacement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for byte_displacement_deferred in 0xB0_u8..=0xBF {
    ///     let reg = Register::from(byte_displacement_deferred);
    ///     assert_eq!(OperandType::ByteDisplacementDeferred(reg),
    ///         OperandType::from(byte_displacement_deferred));
    /// }
    /// ```
    ByteDisplacementDeferred(Register),
    #[doc = include_str!("doc/word_displacement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for word_displacement in 0xC0_u8..=0xCF {
    ///     let reg = Register::from(word_displacement);
    ///     assert_eq!(OperandType::WordDisplacement(reg), OperandType::from(word_displacement));
    /// }
    /// ```
    WordDisplacement(Register),
    #[doc = include_str!("doc/word_displacement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for word_displacement_deferred in 0xD0_u8..=0xDF {
    ///     let reg = Register::from(word_displacement_deferred);
    ///     assert_eq!(OperandType::WordDisplacementDeferred(reg),
    ///         OperandType::from(word_displacement_deferred));
    /// }
    /// ```
    WordDisplacementDeferred(Register),
    #[doc = include_str!("doc/longword_displacement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for longword_displacement in 0xE0_u8..=0xEF {
    ///     let reg = Register::from(longword_displacement);
    ///     assert_eq!(OperandType::LongwordDisplacement(reg),
    ///         OperandType::from(longword_displacement));
    /// }
    /// ```
    LongwordDisplacement(Register),
    #[doc = include_str!("doc/longword_displacement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// for longword_displacement_deferred in 0xF0_u8..=0xFF {
    ///     let reg = Register::from(longword_displacement_deferred);
    ///     assert_eq!(OperandType::LongwordDisplacementDeferred(reg),
    ///         OperandType::from(longword_displacement_deferred));
    /// }
    /// ```
    LongwordDisplacementDeferred(Register),
    #[doc = include_str!("doc/immediate.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// assert_eq!(OperandType::Immediate, OperandType::from(0x8F));
    /// ```
    Immediate,
    #[doc = include_str!("doc/absolute.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use vax_disassembler::operand::{OperandType, Register};
    /// assert_eq!(OperandType::Absolute, OperandType::from(0x9F));
    /// ```
    Absolute,
}

impl From<u8> for OperandType {
    fn from(value: u8) -> OperandType {
        match value {
            0x00..=0x3F => OperandType::Literal(value),
            0x40..=0x4F => OperandType::Indexed(Register::from(value)),
            0x50..=0x5F => OperandType::Register(Register::from(value)),
            0x60..=0x6F => OperandType::RegisterDeferred(Register::from(value)),
            0x70..=0x7F => OperandType::AutoDecrement(Register::from(value)),
            0x80..=0x8E => OperandType::AutoIncrement(Register::from(value)),
            0x8F => OperandType::Immediate,
            0x90..=0x9E => OperandType::AutoIncrementDeferred(Register::from(value)),
            0x9F => OperandType::Absolute,
            0xA0..=0xAF => OperandType::ByteDisplacement(Register::from(value)),
            0xB0..=0xBF => OperandType::ByteDisplacementDeferred(Register::from(value)),
            0xC0..=0xCF => OperandType::WordDisplacement(Register::from(value)),
            0xD0..=0xDF => OperandType::WordDisplacementDeferred(Register::from(value)),
            0xE0..=0xEF => OperandType::LongwordDisplacement(Register::from(value)),
            0xF0..=0xFF => OperandType::LongwordDisplacementDeferred(Register::from(value)),
        }
    }
}

/// # VAX Instruction Operand
///
/// This enum specifies all of the valid VAX instruction operands plus an undefined state.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub enum Operand {
    /// # Undefined operand
    ///
    /// This is used as a placeholder for an operand that hasn't been defined yet. It is equivalent
    /// to the None state without having to use `Option<Operand>` explicitly.
    #[default]
    Undefined,
    #[doc = include_str!("doc/literal.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand};
    /// use std::io::Cursor;
    ///
    /// for literal in 0_u8..=63 {
    ///     assert_eq!(Operand::Literal(literal),
    ///         Cursor::new([literal])
    ///             .read_operand(AccessType::Read, DataType::Byte).unwrap());
    /// }
    /// ```
    Literal(u8),
    #[doc = include_str!("doc/indexed.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for register_deferred in 0x60_u8..=0x6E {
    ///         let reg = Register::from(register_deferred);
    ///         assert_eq!(Operand::Indexed(IndexedOperand::RegisterDeferred(reg), indexed_reg),
    ///             Cursor::new([indexed, register_deferred])
    ///                 .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///     }
    /// }
    /// ```
    Indexed(IndexedOperand, Register),
    #[doc = include_str!("doc/register.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// for register in 0x50_u8..=0x5E {
    ///     let reg = Register::from(register);
    ///     assert_eq!(Operand::Register(reg),
    ///         Cursor::new([register])
    ///             .read_operand(AccessType::Read, DataType::Byte).unwrap());
    /// }
    /// ```
    Register(Register),
    #[doc = include_str!("doc/register_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// for register_deferred in 0x60_u8..=0x6E {
    ///     let reg = Register::from(register_deferred);
    ///     assert_eq!(Operand::RegisterDeferred(reg),
    ///         Cursor::new([register_deferred])
    ///             .read_operand(AccessType::Read, DataType::Byte).unwrap());
    /// }
    /// ```
    RegisterDeferred(Register),
    #[doc = include_str!("doc/autodecrement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// for autodecrement in 0x70_u8..=0x7E {
    ///     let reg = Register::from(autodecrement);
    ///     assert_eq!(Operand::AutoDecrement(reg),
    ///         Cursor::new([autodecrement])
    ///             .read_operand(AccessType::Read, DataType::Byte).unwrap());
    /// }
    /// ```
    AutoDecrement(Register),
    #[doc = include_str!("doc/autoincrement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// for autoincrement in 0x80_u8..=0x8E {
    ///     let reg = Register::from(autoincrement);
    ///     assert_eq!(Operand::AutoIncrement(reg),
    ///         Cursor::new([autoincrement])
    ///             .read_operand(AccessType::Read, DataType::Byte).unwrap());
    /// }
    /// ```
    AutoIncrement(Register),
    #[doc = include_str!("doc/autoincrement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// for autoincrement_deferred in 0x90_u8..=0x9E {
    ///     let reg = Register::from(autoincrement_deferred);
    ///     assert_eq!(Operand::AutoIncrementDeferred(reg),
    ///         Cursor::new([autoincrement_deferred])
    ///             .read_operand(AccessType::Read, DataType::Byte).unwrap());
    /// }
    /// ```
    AutoIncrementDeferred(Register),
    #[doc = include_str!("doc/byte_displacement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const BYTE_OFFSETS: &[i8] = &[-128, -56, -1, 0, 20, 42, 127];
    /// for byte_displacement in 0xA0_u8..=0xAF {
    ///     let reg = Register::from(byte_displacement);
    ///     for byte_offset in BYTE_OFFSETS.iter() {
    ///         assert_eq!(Operand::ByteDisplacement(*byte_offset, reg),
    ///             Cursor::new([byte_displacement, *byte_offset as u8])
    ///                 .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///     }
    /// }
    /// ```
    ByteDisplacement(i8, Register),
    #[doc = include_str!("doc/byte_displacement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const BYTE_OFFSETS: &[i8] = &[-128, -56, -1, 0, 20, 42, 127];
    /// for byte_displacement_deferred in 0xB0_u8..=0xBF {
    ///     let reg = Register::from(byte_displacement_deferred);
    ///     for byte_offset in BYTE_OFFSETS.iter() {
    ///         assert_eq!(Operand::ByteDisplacementDeferred(*byte_offset, reg),
    ///             Cursor::new([byte_displacement_deferred, *byte_offset as u8])
    ///                 .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///     }
    /// }
    /// ```
    ByteDisplacementDeferred(i8, Register),
    #[doc = include_str!("doc/word_displacement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const WORD_OFFSETS: &[i16] = &[-32768, -23456, -9876, -129, 128, 5678, 12345, 32767];
    /// for word_displacement in 0xC0_u8..=0xCF {
    ///     let reg = Register::from(word_displacement);
    ///     for word_offset in WORD_OFFSETS.iter() {
    ///         let word_bytes = word_offset.to_le_bytes();
    ///         assert_eq!(Operand::WordDisplacement(*word_offset, reg),
    ///             Cursor::new([word_displacement, word_bytes[0], word_bytes[1]])
    ///                 .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///     }
    /// }
    /// ```
    WordDisplacement(i16, Register),
    #[doc = include_str!("doc/word_displacement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const WORD_OFFSETS: &[i16] = &[-32768, -23456, -9876, -129, 128, 5678, 12345, 32767];
    /// for word_displacement_deferred in 0xD0_u8..=0xDF {
    ///     let reg = Register::from(word_displacement_deferred);
    ///     for word_offset in WORD_OFFSETS.iter() {
    ///         let word_bytes = word_offset.to_le_bytes();
    ///         assert_eq!(Operand::WordDisplacementDeferred(*word_offset, reg),
    ///             Cursor::new([word_displacement_deferred, word_bytes[0], word_bytes[1]])
    ///                 .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///     }
    /// }
    /// ```
    WordDisplacementDeferred(i16, Register),
    #[doc = include_str!("doc/longword_displacement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const LONGWORD_OFFSETS: &[i32] = &[-2147483648, -12345678, -32769, 32768, 87654321, 2147483647];
    /// for longword_displacement in 0xE0_u8..=0xEF {
    ///     let reg = Register::from(longword_displacement);
    ///     for longword_offset in LONGWORD_OFFSETS.iter() {
    ///         let longword_bytes = longword_offset.to_le_bytes();
    ///         assert_eq!(Operand::LongwordDisplacement(*longword_offset, reg),
    ///             Cursor::new([
    ///                 longword_displacement,
    ///                 longword_bytes[0],
    ///                 longword_bytes[1],
    ///                 longword_bytes[2],
    ///                 longword_bytes[3],
    ///             ]).read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///     }
    /// }
    /// ```
    LongwordDisplacement(i32, Register),
    #[doc = include_str!("doc/longword_displacement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const LONGWORD_OFFSETS: &[i32] = &[-2147483648, -12345678, -32769, 32768, 87654321, 2147483647];
    /// for longword_displacement_deferred in 0xF0_u8..=0xFF {
    ///     let reg = Register::from(longword_displacement_deferred);
    ///     for longword_offset in LONGWORD_OFFSETS.iter() {
    ///         let longword_bytes = longword_offset.to_le_bytes();
    ///         assert_eq!(Operand::LongwordDisplacementDeferred(*longword_offset, reg),
    ///             Cursor::new([
    ///                 longword_displacement_deferred,
    ///                 longword_bytes[0],
    ///                 longword_bytes[1],
    ///                 longword_bytes[2],
    ///                 longword_bytes[3],
    ///             ]).read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///     }
    /// }
    /// ```
    LongwordDisplacementDeferred(i32, Register),
    #[doc = include_str!("doc/immediate.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType, DataValue};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const BYTES: [i8; 5] = [i8::MIN, -1, 64, 100, i8::MAX];
    /// const WORDS: [i16; 5] = [i16::MIN, -129, 128, 23456, i16::MAX];
    /// const LONGWORDS: [i32; 5] = [i32::MIN, -32769, 32768, 987654321, i32::MAX];
    /// const QUADWORDS: [i64; 5] = [i64::MIN, -2147483649, 2147483648, 0xABCDEF123, i64::MAX];
    /// for i in 0..5 {
    ///     let byte_immediate = [0x8F, BYTES[i] as u8];
    ///     assert_eq!(Operand::Immediate(DataValue::Byte(BYTES[i])),
    ///         Cursor::new(byte_immediate)
    ///             .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///     let mut word_immediate = [0x8F, 0, 0];
    ///     word_immediate[1..].copy_from_slice(&WORDS[i].to_le_bytes());
    ///     assert_eq!(Operand::Immediate(DataValue::Word(WORDS[i])),
    ///         Cursor::new(word_immediate)
    ///             .read_operand(AccessType::Read, DataType::Word).unwrap());
    ///     let mut longword_immediate = [0x8F, 0, 0, 0, 0];
    ///     longword_immediate[1..].copy_from_slice(&LONGWORDS[i].to_le_bytes());
    ///     assert_eq!(Operand::Immediate(DataValue::Longword(LONGWORDS[i])),
    ///         Cursor::new(longword_immediate)
    ///             .read_operand(AccessType::Read, DataType::Longword).unwrap());
    ///     let mut quadword_immediate = [0x8F, 0, 0, 0, 0, 0, 0, 0, 0];
    ///     quadword_immediate[1..].copy_from_slice(&QUADWORDS[i].to_le_bytes());
    ///     assert_eq!(Operand::Immediate(DataValue::Quadword(QUADWORDS[i])),
    ///         Cursor::new(quadword_immediate)
    ///             .read_operand(AccessType::Read, DataType::Quadword).unwrap());
    /// }
    /// ```
    Immediate(DataValue),
    #[doc = include_str!("doc/absolute.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const ADDRESSES: &[u32] = &[0x0, 0x200, 0x80000000, 0x81234567, 0xBFFFFFFF, 0xFFFFFFFF];
    /// for address in ADDRESSES.iter() {
    ///     let address_bytes = address.to_le_bytes();
    ///     assert_eq!(Operand::Absolute(*address),
    ///         Cursor::new([
    ///             0x9F,
    ///             address_bytes[0],
    ///             address_bytes[1],
    ///             address_bytes[2],
    ///             address_bytes[3],
    ///         ]).read_operand(AccessType::Read, DataType::Byte).unwrap());
    /// }
    /// ```
    Absolute(u32),
    /// # Branch
    ///
    /// This is a special mode determined by the operand's access type of branch. There is no
    /// operand code, just a branch offset from the address after reading the offset value.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType, DataValue};
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const BYTE_OFFSETS: [i8; 9] = [-128, -100, -39, -20, 0, 30, 42, 100, 127];
    /// const WORD_OFFSETS: [i16; 9] = [-32768, -23456, -1234, -129, 128, 512, 1234, 23456, 32767];
    /// for i in 0..9 {
    ///     let word_bytes = WORD_OFFSETS[i].to_le_bytes();
    ///     assert_eq!(Operand::Branch(DataValue::Byte(BYTE_OFFSETS[i])),
    ///         Cursor::new([BYTE_OFFSETS[i] as u8])
    ///             .read_operand(AccessType::Branch, DataType::Byte).unwrap());
    ///     assert_eq!(Operand::Branch(DataValue::Word(WORD_OFFSETS[i])),
    ///         Cursor::new(word_bytes)
    ///             .read_operand(AccessType::Branch, DataType::Word).unwrap());
    /// }
    /// ```
    Branch(DataValue),
}

/// # VAX Instruction Indexed Operand
///
/// This enum specifies all of the valid VAX instruction operands that can be part of an indexed
/// addressing mode.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum IndexedOperand {
    #[doc = include_str!("doc/register_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for register_deferred in 0x60_u8..=0x6E {
    ///         let reg = Register::from(register_deferred);
    ///         assert_eq!(Operand::Indexed(IndexedOperand::RegisterDeferred(reg), indexed_reg),
    ///             Cursor::new([indexed, register_deferred])
    ///                 .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///     }
    /// }
    /// ```
    RegisterDeferred(Register),
    #[doc = include_str!("doc/autodecrement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for autodecrement in 0x70_u8..=0x7E {
    ///         let reg = Register::from(autodecrement);
    ///         if indexed_reg != reg {
    ///             assert_eq!(Operand::Indexed(IndexedOperand::AutoDecrement(reg), indexed_reg),
    ///                 Cursor::new([indexed, autodecrement])
    ///                     .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///         }
    ///     }
    /// }
    /// ```
    AutoDecrement(Register),
    #[doc = include_str!("doc/autoincrement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for autoincrement in 0x80_u8..=0x8E {
    ///         let reg = Register::from(autoincrement);
    ///         if indexed_reg != reg {
    ///             assert_eq!(Operand::Indexed(IndexedOperand::AutoIncrement(reg), indexed_reg),
    ///                 Cursor::new([indexed, autoincrement])
    ///                     .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///         }
    ///     }
    /// }
    /// ```
    AutoIncrement(Register),
    #[doc = include_str!("doc/autoincrement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for autoincrement_deferred in 0x90_u8..=0x9E {
    ///         let reg = Register::from(autoincrement_deferred);
    ///         if indexed_reg != reg {
    ///             assert_eq!(Operand::Indexed(IndexedOperand::AutoIncrementDeferred(reg),
    ///                 indexed_reg), Cursor::new([indexed, autoincrement_deferred])
    ///                     .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///         }
    ///     }
    /// }
    /// ```
    AutoIncrementDeferred(Register),
    #[doc = include_str!("doc/byte_displacement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const BYTE_OFFSETS: &[i8] = &[-128, -56, -1, 0, 20, 42, 127];
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for byte_displacement in 0xA0_u8..=0xAF {
    ///         let reg = Register::from(byte_displacement);
    ///         for byte_offset in BYTE_OFFSETS.iter() {
    ///             assert_eq!(Operand::Indexed(
    ///                 IndexedOperand::ByteDisplacement(*byte_offset, reg), indexed_reg),
    ///                 Cursor::new([indexed, byte_displacement, *byte_offset as u8])
    ///                     .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///         }
    ///     }
    /// }
    /// ```
    ByteDisplacement(i8, Register),
    #[doc = include_str!("doc/byte_displacement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const BYTE_OFFSETS: &[i8] = &[-128, -56, -1, 0, 20, 42, 127];
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for byte_displacement_deferred in 0xB0_u8..=0xBF {
    ///         let reg = Register::from(byte_displacement_deferred);
    ///         for byte_offset in BYTE_OFFSETS.iter() {
    ///             assert_eq!(Operand::Indexed(
    ///                 IndexedOperand::ByteDisplacementDeferred(*byte_offset, reg), indexed_reg),
    ///                 Cursor::new([indexed, byte_displacement_deferred, *byte_offset as u8])
    ///                     .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///         }
    ///     }
    /// }
    /// ```
    ByteDisplacementDeferred(i8, Register),
    #[doc = include_str!("doc/word_displacement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const WORD_OFFSETS: &[i16] = &[-32768, -23456, -9876, -129, 128, 5678, 12345, 32767];
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for word_displacement in 0xC0_u8..=0xCF {
    ///         let reg = Register::from(word_displacement);
    ///         for word_offset in WORD_OFFSETS.iter() {
    ///             let word_bytes = word_offset.to_le_bytes();
    ///             assert_eq!(Operand::Indexed(
    ///                 IndexedOperand::WordDisplacement(*word_offset, reg), indexed_reg),
    ///                 Cursor::new([indexed, word_displacement, word_bytes[0], word_bytes[1]])
    ///                     .read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///         }
    ///     }
    /// }
    /// ```
    WordDisplacement(i16, Register),
    #[doc = include_str!("doc/word_displacement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const WORD_OFFSETS: &[i16] = &[-32768, -23456, -9876, -129, 128, 5678, 12345, 32767];
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for word_displacement_deferred in 0xD0_u8..=0xDF {
    ///         let reg = Register::from(word_displacement_deferred);
    ///         for word_offset in WORD_OFFSETS.iter() {
    ///             let word_bytes = word_offset.to_le_bytes();
    ///             assert_eq!(Operand::Indexed(
    ///                 IndexedOperand::WordDisplacementDeferred(*word_offset, reg), indexed_reg),
    ///                 Cursor::new([
    ///                     indexed,
    ///                     word_displacement_deferred,
    ///                     word_bytes[0],
    ///                     word_bytes[1],
    ///                 ]).read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///         }
    ///     }
    /// }
    /// ```
    WordDisplacementDeferred(i16, Register),
    #[doc = include_str!("doc/longword_displacement.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const LONGWORD_OFFSETS: &[i32] = &[-2147483648, -12345678, -32769, 32768, 87654321, 2147483647];
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for longword_displacement in 0xE0_u8..=0xEF {
    ///         let reg = Register::from(longword_displacement);
    ///         for longword_offset in LONGWORD_OFFSETS.iter() {
    ///             let longword_bytes = longword_offset.to_le_bytes();
    ///             assert_eq!(Operand::Indexed(
    ///                 IndexedOperand::LongwordDisplacement(*longword_offset, reg), indexed_reg),
    ///                 Cursor::new([
    ///                     indexed,
    ///                     longword_displacement,
    ///                     longword_bytes[0],
    ///                     longword_bytes[1],
    ///                     longword_bytes[2],
    ///                     longword_bytes[3],
    ///                 ]).read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///         }
    ///     }
    /// }
    /// ```
    LongwordDisplacement(i32, Register),
    #[doc = include_str!("doc/longword_displacement_deferred.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const LONGWORD_OFFSETS: &[i32] = &[-2147483648, -12345678, -32769, 32768, 87654321, 2147483647];
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for longword_displacement_deferred in 0xF0_u8..=0xFF {
    ///         let reg = Register::from(longword_displacement_deferred);
    ///         for longword_offset in LONGWORD_OFFSETS.iter() {
    ///             let longword_bytes = longword_offset.to_le_bytes();
    ///             assert_eq!(Operand::Indexed(
    ///                 IndexedOperand::LongwordDisplacementDeferred(*longword_offset, reg), indexed_reg),
    ///                 Cursor::new([
    ///                     indexed,
    ///                     longword_displacement_deferred,
    ///                     longword_bytes[0],
    ///                     longword_bytes[1],
    ///                     longword_bytes[2],
    ///                     longword_bytes[3],
    ///                 ]).read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///         }
    ///     }
    /// }
    /// ```
    LongwordDisplacementDeferred(i32, Register),
    #[doc = include_str!("doc/absolute.txt")]
    ///
    /// ## Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use vax_disassembler::operand::{IndexedOperand, Operand, ReadOperand, Register};
    /// use std::io::Cursor;
    ///
    /// const ADDRESSES: &[u32] = &[0x0, 0x200, 0x80000000, 0x81234567, 0xBFFFFFFF, 0xFFFFFFFF];
    /// for indexed in 0x40_u8..=0x4E {
    ///     let indexed_reg = Register::from(indexed);
    ///     for address in ADDRESSES.iter() {
    ///         let address_bytes = address.to_le_bytes();
    ///         assert_eq!(Operand::Indexed(IndexedOperand::Absolute(*address), indexed_reg),
    ///             Cursor::new([
    ///                 indexed,
    ///                 0x9F,
    ///                 address_bytes[0],
    ///                 address_bytes[1],
    ///                 address_bytes[2],
    ///                 address_bytes[3],
    ///             ]).read_operand(AccessType::Read, DataType::Byte).unwrap());
    ///     }
    /// }
    /// ```
    Absolute(u32),
}

impl TryFrom<Operand> for IndexedOperand {
    type Error = Error;

    fn try_from(operand: Operand) -> Result<IndexedOperand> {
        match operand {
            Operand::RegisterDeferred(reg) => Ok(IndexedOperand::RegisterDeferred(reg)),
            Operand::AutoDecrement(reg) => Ok(IndexedOperand::AutoDecrement(reg)),
            Operand::AutoIncrement(reg) => Ok(IndexedOperand::AutoIncrement(reg)),
            Operand::AutoIncrementDeferred(reg) => Ok(IndexedOperand::AutoIncrementDeferred(reg)),
            Operand::ByteDisplacement(value, reg) => Ok(IndexedOperand::ByteDisplacement(value, reg)),
            Operand::ByteDisplacementDeferred(value, reg) => Ok(IndexedOperand::ByteDisplacementDeferred(value, reg)),
            Operand::WordDisplacement(value, reg) => Ok(IndexedOperand::WordDisplacement(value, reg)),
            Operand::WordDisplacementDeferred(value, reg) => Ok(IndexedOperand::WordDisplacementDeferred(value, reg)),
            Operand::LongwordDisplacement(value, reg) => Ok(IndexedOperand::LongwordDisplacement(value, reg)),
            Operand::LongwordDisplacementDeferred(value, reg) => Ok(IndexedOperand::LongwordDisplacementDeferred(value, reg)),
            // Immediate behavior is always unpredictable. I may support this in the future.
            //Operand::Immediate(value) => Ok(IndexedOperand::Immediate(value)),
            Operand::Absolute(value) => Ok(IndexedOperand::Absolute(value)),
            other => Err(Error::InvalidIndexedOperand(other)),
        }
    }
}

impl From<IndexedOperand> for Operand {
    fn from(operand: IndexedOperand) -> Operand {
        match operand {
            IndexedOperand::RegisterDeferred(reg) => Operand::RegisterDeferred(reg),
            IndexedOperand::AutoDecrement(reg) => Operand::AutoDecrement(reg),
            IndexedOperand::AutoIncrement(reg) => Operand::AutoIncrement(reg),
            IndexedOperand::AutoIncrementDeferred(reg) => Operand::AutoIncrementDeferred(reg),
            IndexedOperand::ByteDisplacement(value, reg) => Operand::ByteDisplacement(value, reg),
            IndexedOperand::ByteDisplacementDeferred(value, reg) => Operand::ByteDisplacementDeferred(value, reg),
            IndexedOperand::WordDisplacement(value, reg) => Operand::WordDisplacement(value, reg),
            IndexedOperand::WordDisplacementDeferred(value, reg) => Operand::WordDisplacementDeferred(value, reg),
            IndexedOperand::LongwordDisplacement(value, reg) => Operand::LongwordDisplacement(value, reg),
            IndexedOperand::LongwordDisplacementDeferred(value, reg) => Operand::LongwordDisplacementDeferred(value, reg),
            // Immediate behavior is always unpredictable. I may support this in the future.
            //IndexedOperand::Immediate(value) => Operand::Immediate(value),
            IndexedOperand::Absolute(value) => Operand::Absolute(value),
        }
    }
}

fn display_no_pc<T: Display>(f: &mut Formatter, lead: &str, value: T, reg: &Register) -> fmt::Result {
    if &Register::PC == reg {
        write!(f, "{}{}", lead, value)
    }
    else {
        write!(f, "{}{}({})", lead, value, reg)
    }
}

impl Display for Operand {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Operand::*;
        match self {
            Undefined => f.write_str("Error: Undefined Operand"),
            Literal(value) => write!(f, "S^#{}", value),
            Indexed(operand, reg) => write!(f, "{}[{}]", operand, reg),
            Register(reg) => write!(f, "{}", reg),
            RegisterDeferred(reg) => write!(f, "({})", reg),
            AutoDecrement(reg) => write!(f, "-({0})", reg),
            AutoIncrement(reg) => write!(f, "({0})+", reg),
            AutoIncrementDeferred(reg) => write!(f, "@({0})+", reg),
            ByteDisplacement(value, reg) => display_no_pc(f, "B^", value, reg),
            ByteDisplacementDeferred(value, reg) => display_no_pc(f, "@B^", value, reg),
            WordDisplacement(value, reg) => display_no_pc(f, "W^", value, reg),
            WordDisplacementDeferred(value, reg) => display_no_pc(f, "@W^", value, reg),
            LongwordDisplacement(value, reg) => display_no_pc(f, "L^", value, reg),
            LongwordDisplacementDeferred(value, reg) => display_no_pc(f, "@L^", value, reg),
            Immediate(value) => write!(f, "#{0}", value),
            Absolute(value) => write!(f, "@#{0}", value),
            Branch(value) => write!(f, "{0}", value),
        }
    }
}

impl Display for IndexedOperand {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Operand::from(*self).fmt(f)
    }
}

/// Extends [`Read`] with a method to read a VAX operand ([`Operand`]).
///
/// # Examples
///
/// ```rust
/// use vax_disassembler::opcode::{AccessType, DataType, DataValue};
/// use vax_disassembler::operand::{Operand, ReadOperand};
/// use std::io::Cursor;
///
/// assert_eq!(Cursor::new([30]).read_operand(AccessType::Branch, DataType::Byte).unwrap(),
///     Operand::Branch(DataValue::Byte(30)));
///
/// for quadword in (i64::MIN..=i64::MAX).step_by(u64::MAX as usize / 241) {
///     let mut buffer = [0u8; 9];
///     buffer[0] = 0x8F;   // Immediate
///     buffer[1..].copy_from_slice(&quadword.to_le_bytes());
///     let mut reader = Cursor::new(buffer);
///     let data_value = reader.read_operand(AccessType::Read, DataType::Quadword).unwrap();
///     assert_eq!(data_value, Operand::Immediate(DataValue::Quadword(quadword)));
/// }
/// ```
pub trait ReadOperand: Read + ReadDataValue {
    /// Read in a `MACRO32` operand from a reader.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use vax_disassembler::operand::{Operand, ReadOperand, Register};
    /// use vax_disassembler::opcode::{AccessType, DataType};
    /// use std::io::Read;
    ///
    /// for byte_branch in i8::MIN..=i8::MAX {
    ///     let mut reader = std::io::Cursor::new([byte_branch as u8]);
    ///     let output = reader.read_operand(AccessType::Branch, DataType::Byte).unwrap();
    /// }
    /// for literal in 0_u8..=63 {
    ///     let mut reader = std::io::Cursor::new([literal]);
    ///     let output = reader.read_operand(AccessType::Read, DataType::Byte).unwrap();
    ///     assert_eq!(Operand::Literal(literal), output);
    /// }
    /// for reg in 0x50..=0x5E {
    ///     let mut reader = std::io::Cursor::new([reg]);
    ///     let output = reader.read_operand(AccessType::Read, DataType::Word).unwrap();
    ///     assert_eq!(Operand::Register(Register::from(reg)), output);
    /// }
    /// ```
    fn read_operand(&mut self, access: AccessType, size: DataType) -> Result<Operand> {
        match access {
            AccessType::Branch => Ok(Operand::Branch(self.read_data_value(size)?)),
            _ => {
                let mut buf = [0; 1];
                self.read_exact(&mut buf)?;
                match OperandType::from(buf[0]) {
                    OperandType::Literal(lit) => Ok(Operand::Literal(lit)),
                    OperandType::Indexed(reg) =>
                        Ok(Operand::Indexed(IndexedOperand::try_from(self.read_operand(access, size)?)?, reg)),
                    OperandType::Register(reg) => Ok(Operand::Register(reg)),
                    OperandType::RegisterDeferred(reg) => Ok(Operand::RegisterDeferred(reg)),
                    OperandType::AutoDecrement(reg) => Ok(Operand::AutoDecrement(reg)),
                    OperandType::AutoIncrement(reg) => Ok(Operand::AutoIncrement(reg)),
                    OperandType::AutoIncrementDeferred(reg) =>
                        Ok(Operand::AutoIncrementDeferred(reg)),
                    OperandType::ByteDisplacement(reg) => {
                        let mut buf = [0; 1];
                        self.read_exact(&mut buf)?;
                        Ok(Operand::ByteDisplacement(buf[0] as i8, reg))
                    }
                    OperandType::ByteDisplacementDeferred(reg) => {
                        let mut buf = [0; 1];
                        self.read_exact(&mut buf)?;
                        Ok(Operand::ByteDisplacementDeferred(buf[0] as i8, reg))
                    }
                    OperandType::WordDisplacement(reg) => {
                        let mut buf = [0; 2];
                        self.read_exact(&mut buf)?;
                        Ok(Operand::WordDisplacement(i16::from_le_bytes(buf), reg))
                    }
                    OperandType::WordDisplacementDeferred(reg) => {
                        let mut buf = [0; 2];
                        self.read_exact(&mut buf)?;
                        Ok(Operand::WordDisplacementDeferred(i16::from_le_bytes(buf), reg))
                    }
                    OperandType::LongwordDisplacement(reg) => {
                        let mut buf = [0; 4];
                        self.read_exact(&mut buf)?;
                        Ok(Operand::LongwordDisplacement(i32::from_le_bytes(buf), reg))
                    }
                    OperandType::LongwordDisplacementDeferred(reg) => {
                        let mut buf = [0; 4];
                        self.read_exact(&mut buf)?;
                        Ok(Operand::LongwordDisplacementDeferred(i32::from_le_bytes(buf), reg))
                    }
                    OperandType::Immediate => Ok(Operand::Immediate(self.read_data_value(size)?)),
                    OperandType::Absolute => {
                        let mut buf = [0; 4];
                        self.read_exact(&mut buf)?;
                        Ok(Operand::Absolute(u32::from_le_bytes(buf)))
                    }
                }
            }
        }
    }
}

/// All types that implement `Read` get methods defined in `ReadMacro32` for free.
impl<R: Read + ?Sized> ReadOperand for R {}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Get data_value() strategy.
    use crate::opcode::{
        WriteDataValue,
        data_value_tests::data_value,
    };

    const OPTYP_STD: usize = 36;
    const OPTYP_LITERAL: usize = 8;
    const OPTYP_REGISTER: usize = 27;
    prop_compose! {
        fn operand_type(limit: usize)(select in 0..=limit) -> (AccessType, DataType) {
            match select {
    			 0 => (AccessType::Read, DataType::Byte),
    			 1 => (AccessType::Read, DataType::Word),
    			 2 => (AccessType::Read, DataType::Longword),
    			 3 => (AccessType::Read, DataType::Quadword),
    			 4 => (AccessType::Read, DataType::Octoword),
    			 5 => (AccessType::Read, DataType::Floating),
    			 6 => (AccessType::Read, DataType::Double),
    			 7 => (AccessType::Read, DataType::GFloating),
    			 8 => (AccessType::Read, DataType::HFloating),
    			 9 => (AccessType::Write, DataType::Byte),
    			10 => (AccessType::Write, DataType::Word),
    			11 => (AccessType::Write, DataType::Longword),
    			12 => (AccessType::Write, DataType::Quadword),
    			13 => (AccessType::Write, DataType::Octoword),
    			14 => (AccessType::Write, DataType::Floating),
    			15 => (AccessType::Write, DataType::Double),
    			16 => (AccessType::Write, DataType::GFloating),
    			17 => (AccessType::Write, DataType::HFloating),
    			18 => (AccessType::Modify, DataType::Byte),
    			19 => (AccessType::Modify, DataType::Word),
    			20 => (AccessType::Modify, DataType::Longword),
    			21 => (AccessType::Modify, DataType::Quadword),
    			22 => (AccessType::Modify, DataType::Octoword),
    			23 => (AccessType::Modify, DataType::Floating),
    			24 => (AccessType::Modify, DataType::Double),
    			25 => (AccessType::Modify, DataType::GFloating),
    			26 => (AccessType::Modify, DataType::HFloating),
    			27 => (AccessType::VariableBitField, DataType::Byte),
    			28 => (AccessType::Address, DataType::Byte),
    			29 => (AccessType::Address, DataType::Word),
    			30 => (AccessType::Address, DataType::Longword),
    			31 => (AccessType::Address, DataType::Quadword),
    			32 => (AccessType::Address, DataType::Octoword),
    			33 => (AccessType::Address, DataType::Floating),
    			34 => (AccessType::Address, DataType::Double),
    			35 => (AccessType::Address, DataType::GFloating),
    			36 => (AccessType::Address, DataType::HFloating),
    			 _ => (AccessType::Read, DataType::Byte),
            }
        }
    }

    prop_compose! {
        fn literal()(
            literal in 0_u8..=63,
            (access, size) in operand_type(OPTYP_LITERAL),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            (Operand::Literal(literal), vec![literal], access, size)
        }
    }

    prop_compose! {
        fn register()(
            register in 0x50_u8..=0x5E,
            (access, size) in operand_type(OPTYP_REGISTER),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            (Operand::Register(Register::from(register)), vec![register], access, size)
        }
    }

    prop_compose! {
        fn register_deferred()(
            register in 0x60_u8..=0x6E,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            (Operand::RegisterDeferred(Register::from(register)), vec![register], access, size)
        }
    }

    prop_compose! {
        fn auto_decrement()(
            register in 0x70_u8..=0x7E,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            (Operand::AutoDecrement(Register::from(register)), vec![register], access, size)
        }
    }

    prop_compose! {
        fn auto_increment()(
            register in 0x80_u8..=0x8E,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            (Operand::AutoIncrement(Register::from(register)), vec![register], access, size)
        }
    }

    prop_compose! {
        fn auto_increment_deferred()(
            register in 0x90_u8..=0x9E,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            (Operand::AutoIncrementDeferred(Register::from(register)), vec![register], access, size)
        }
    }

    prop_compose! {
        fn byte_displacement()(
            register in 0xA0_u8..=0xAF,
            disp in i8::MIN..=i8::MAX,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            (Operand::ByteDisplacement(disp, Register::from(register)), vec![register, disp as u8], access, size)
        }
    }

    prop_compose! {
        fn byte_displacement_deferred()(
            register in 0xB0_u8..=0xBF,
            disp in i8::MIN..=i8::MAX,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            (Operand::ByteDisplacementDeferred(disp, Register::from(register)), vec![register, disp as u8], access, size)
        }
    }

    prop_compose! {
        fn word_displacement()(
            register in 0xC0_u8..=0xCF,
            disp in i16::MIN..=i16::MAX,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            let mut buf = Vec::with_capacity(3);
            buf.push(register);
            buf.extend_from_slice(&disp.to_le_bytes());
            (Operand::WordDisplacement(disp, Register::from(register)), buf, access, size)
        }
    }

    prop_compose! {
        fn word_displacement_deferred()(
            register in 0xD0_u8..=0xDF,
            disp in i16::MIN..=i16::MAX,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            let mut buf = Vec::with_capacity(3);
            buf.push(register);
            buf.extend_from_slice(&disp.to_le_bytes());
            (Operand::WordDisplacementDeferred(disp, Register::from(register)), buf, access, size)
        }
    }

    prop_compose! {
        fn longword_displacement()(
            register in 0xE0_u8..=0xEF,
            disp in i32::MIN..=i32::MAX,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            let mut buf = Vec::with_capacity(5);
            buf.push(register);
            buf.extend_from_slice(&disp.to_le_bytes());
            (Operand::LongwordDisplacement(disp, Register::from(register)), buf, access, size)
        }
    }

    prop_compose! {
        fn longword_displacement_deferred()(
            register in 0xF0_u8..=0xFF,
            disp in i32::MIN..=i32::MAX,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            let mut buf = Vec::with_capacity(5);
            buf.push(register);
            buf.extend_from_slice(&disp.to_le_bytes());
            (Operand::LongwordDisplacementDeferred(disp, Register::from(register)), buf, access, size)
        }
    }

    prop_compose! {
        fn absolute()(
            disp in u32::MIN..=u32::MAX,
            (access, size) in operand_type(OPTYP_STD),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            let mut buf = Vec::with_capacity(5);
            buf.push(0x9F);
            buf.extend_from_slice(&disp.to_le_bytes());
            (Operand::Absolute(disp), buf, access, size)
        }
    }

    fn indexable_operand() -> BoxedStrategy<(Operand, Vec<u8>, AccessType, DataType)> {
        prop_oneof![
            register_deferred(),
            auto_decrement(),
            auto_increment(),
            auto_increment_deferred(),
            byte_displacement(),
            byte_displacement_deferred(),
            word_displacement(),
            word_displacement_deferred(),
            longword_displacement(),
            longword_displacement_deferred(),
            absolute(),
        ].boxed()
    }

    prop_compose! {
        fn indexed()(
            (i_operand, i_buf, access, size) in indexable_operand(),
            mut register in 0x40_u8..=0x4E,
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            let i_operand = match IndexedOperand::try_from(i_operand) {
                Ok(op) => op,
                // This should never happen. Default to basic operand.
                Err(_) => IndexedOperand::RegisterDeferred(Register::R0),
            };
            match i_operand {
                IndexedOperand::AutoDecrement(i_reg) |
                IndexedOperand::AutoIncrement(i_reg) |
                IndexedOperand::AutoIncrementDeferred(i_reg) => {
                    if i_reg == Register::from(register) {
                        // If index register is the same as the indexed register, wrap around to a
                        // different register.
                        if 0x4E == register {
                            register = 0x40;
                        }
                        else {
                            register += 1;
                        }
                    }
                }
                _ => {}
            }
            let mut buf = Vec::with_capacity(1 + i_buf.len());
            buf.push(register);
            buf.extend_from_slice(&i_buf);
            (Operand::Indexed(i_operand, Register::from(register)), buf, access, size)
        }
    }

    prop_compose! {
        fn immediate()(
            value in data_value(),
        ) -> (Operand, Vec<u8>, AccessType, DataType) {
            let mut buf = Vec::new();
            buf.push(0x8F);
            let _ = buf.write_data_value(value); // Ignore any error.
            (Operand::Immediate(value), buf, AccessType::Read, value.data_type())
        }
    }

    fn branch() -> impl Strategy<Value = (Operand, Vec<u8>, AccessType, DataType)> {
        prop_oneof![
            any::<i8>().prop_map(|x| (
                Operand::Branch(DataValue::Byte(x)),
                vec![x as u8],
                AccessType::Branch,
                DataType::Byte)),
        ]
    }

    fn valid_operand() -> BoxedStrategy<(Operand, Vec<u8>, AccessType, DataType)> {
        prop_oneof![
            literal(),
            indexed(),
            register(),
            register_deferred(),
            auto_decrement(),
            auto_increment(),
            auto_increment_deferred(),
            byte_displacement(),
            byte_displacement_deferred(),
            word_displacement(),
            word_displacement_deferred(),
            longword_displacement(),
            longword_displacement_deferred(),
            immediate(),
            absolute(),
            branch(),
        ].boxed()
    }

    proptest! {
        #[test]
        fn valid_read_operands((operand, input, access, size) in valid_operand()) {
            let mut reader = std::io::Cursor::new(input);
            prop_assert_eq!(reader.read_operand(access, size)?, operand);
        }
    }
}
