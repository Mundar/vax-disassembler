//! # Disassembly Errors

use thiserror::Error;
use crate::{
    opcode::{AccessType, DataType},
    operand::Operand,
};

/// # VAX assembler/disassembler errors
///
/// # Examples
///
/// ```rust
/// use std::io::Cursor;
/// use vax_disassembler::{ReadMacro32, error::Error};
///
/// let invalid_opcode = Cursor::new([0x57]).disassemble();
/// assert!(invalid_opcode.is_err());
/// if let Err(Error::InvalidOpcode(0x57)) = invalid_opcode {} else { panic!(); }
/// ```
#[derive(Debug, Error)]
pub enum Error {
    /// # Invalid Opcode
    ///
    /// In the documention, all undefined opcodes are marked as "Reserved to DIGITAL", so this
    /// error is like a reserved operand error.
    #[error("Invalid opcode: {0:#X}")]
    InvalidOpcode(u16),

    /// # Invalid Opcode String
    ///
    /// In the documention, all undefined opcodes are marked as "Reserved to DIGITAL", so this
    /// error is like a reserved operand error.
    #[error("Invalid opcode: {0}")]
    InvalidOpcodeString(String),

    /// # Invalid Indexed Operand
    ///
    /// 
    #[error("Invalid indexed operand: {0:?}")]
    InvalidIndexedOperand(Operand),

    /// # Invalid Access Type and Data Type Combination
    #[error("Invalid access type and data size: access = {0:?}, size = {0:?}")]
    InvalidAccessSize(AccessType, DataType),

    /// # Unimplemented Feature
    ///
    /// This is an unimplemented feature. This error should go away once development is complete.
    #[error("Unimpleneted feature: {0}")]
    Unimplemented(&'static str),

    /// # Passtrhough I/O Error
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
}

/// Error handling with the `Result` type for the [`enum@Error`] type.
pub type Result<T> = std::result::Result<T, Error>;
