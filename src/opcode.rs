//! # MACRO32 Opcodes

use std::{
    convert::TryFrom,
    fmt::{self, Display, Formatter},
    io::{Read, Write},
};
use vax_floating::{FFloating, DFloating, GFloating, HFloating};
use crate::{
    error::{Error, Result},
    operand::{Operand},
};

/// # VAX Operand Access Type
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AccessType {
    /// # Address
    ///
    /// The address of the specified operand in the form of a longword is the actual instruction
    /// operand. The specified operand is not accessed directly although the instruction may
    /// subsequently use the address to access that operand.
    Address,
    /// # Branch
    ///
    /// No operand is accessed. The operand specifier itself is a branch displacement.
    Branch,
    /// # Modify
    ///
    /// The specified operand is read, potentially modified, and written. This is not done under a
    /// memory interlock.
    Modify,
    /// # Read
    ///
    /// The specified operand is read only.
    Read,
    /// # Variable-length bit field base address
    ///
    /// This is the same as address access type except for register mode. In register mode, the
    /// field is contained in register n designated by the operand specifier (or register n + 1
    /// concatenated with register n). This access type is a special variant of the address access
    /// type.
    VariableBitField,
    /// # Write
    ///
    /// The specified operand is written only.
    Write,
}

macro_rules! define_data_functions {
    ($(($desc: ident, $count: expr, $out: ty, $display: literal),)+) => {
        /// # VAX Data Types
        #[derive(Copy, Clone, Debug, PartialEq, Eq)]
        pub enum DataType {
            $(
                #[doc = concat!("The VAX ", stringify!($desc), " data type. Reads into a Rust ",
                    stringify!($out), " value.")]
                $desc,
            )+
        }

        /// # Vax Data Values
        #[derive(Copy, Clone, Debug, PartialEq, Eq)]
        pub enum DataValue {
            $(
                #[doc = concat!("The VAX ", stringify!($desc), " data type. Reads into a `",
                    stringify!($out), "` value.")]
                $desc($out),
            )+
        }

        impl DataValue {
            /// Return the [`DataType`] for this `DataValue`.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::opcode::{DataType, DataValue};
            /// use vax_floating::{FFloating, DFloating, GFloating, HFloating};
            ///
            $(
                #[doc = concat!("assert_eq!(DataValue::", stringify!($desc), "(", stringify!($out),
                    "::MAX).data_type(), DataType::", stringify!($desc), ");")]
            )+
            /// ```
            pub const fn data_type(&self) -> DataType {
                match self {
                    $(
                    DataValue::$desc(_) => DataType::$desc,
                    )+
                }
            }

            /// Return the size in bytes for this `DataValue`.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::opcode::DataValue;
            /// use vax_floating::{FFloating, DFloating, GFloating, HFloating};
            ///
            $(
                #[doc = concat!("assert_eq!(DataValue::", stringify!($desc), "(", stringify!($out),
                    "::MAX).len(), ", stringify!($count), ");")]
            )+
            /// ```
            pub const fn len(&self) -> usize {
                match self {
                    $(
                    DataValue::$desc(_) => $count,
                    )+
                }
            }
        }

        impl Display for DataValue {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                match self {
                    $(
                    DataValue::$desc(value) => write!(f, $display, value),
                    )+
                }
            }
        }

        /// Extends [`Read`] with a method to read a VAX data type ([`DataType`]) into the enum
        /// [`DataValue`].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use vax_disassembler::{DataType, DataValue, ReadDataValue};
        /// use std::io::Cursor;
        ///
        /// for quadword in (i64::MIN..=i64::MAX).step_by(u64::MAX as usize / 241) {
        ///     let mut reader = Cursor::new(quadword.to_le_bytes());
        ///     let data_value = reader.read_data_value(DataType::Quadword).unwrap();
        ///     assert_eq!(data_value, DataValue::Quadword(quadword));
        /// }
        /// ```
        pub trait ReadDataValue: Read {
            /// Reads in a specified VAX data type ([`DataType`]) and returns the [`DataValue`].
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::{DataType, DataValue, ReadDataValue};
            /// use std::io::Cursor;
            ///
            /// for byte in i8::MIN..=i8::MAX {
            ///     let mut reader = Cursor::new([byte as u8]);
            ///     let data_value = reader.read_data_value(DataType::Byte).unwrap();
            ///     assert_eq!(data_value, DataValue::Byte(byte));
            /// }
            /// for word in (i16::MIN..=i16::MAX).step_by(u16::MAX as usize / 257) {
            ///     let mut reader = Cursor::new(word.to_le_bytes());
            ///     let data_value = reader.read_data_value(DataType::Word).unwrap();
            ///     assert_eq!(data_value, DataValue::Word(word));
            /// }
            /// for longword in (i32::MIN..=i32::MAX).step_by(u32::MAX as usize / 251) {
            ///     let mut reader = Cursor::new(longword.to_le_bytes());
            ///     let data_value = reader.read_data_value(DataType::Longword).unwrap();
            ///     assert_eq!(data_value, DataValue::Longword(longword));
            /// }
            /// ```
            fn read_data_value(&mut self, data_type: DataType) -> Result<DataValue> {
                match data_type {
                    $(
                        DataType::$desc => {
                            let mut buf = [0; $count];
                            self.read_exact(&mut buf)?;
                            Ok(DataValue::$desc(<$out>::from_le_bytes(buf)))
                        }
                    )+
                }
            }
        }

        /// All types that implement `Read` get methods defined in `ReadDataValue` for free.
        impl<R: Read + ?Sized> ReadDataValue for R {}

        /// Extends [`Write`] with a method to write a VAX data value ([`DataValue`]).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use vax_disassembler::{DataValue, WriteDataValue};
        /// use std::io::Cursor;
        ///
        /// for quadword in (i64::MIN..=i64::MAX).step_by(u64::MAX as usize / 241) {
        ///     let value = DataValue::Quadword(quadword);
        ///     let mut writer = Vec::with_capacity(8);
        ///     writer.write_data_value(value).unwrap();
        ///     assert_eq!(&writer, &quadword.to_le_bytes());
        /// }
        /// ```
        pub trait WriteDataValue: Write {
            /// Writes in a specified VAX data value (`DataValue`).
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::{DataType, DataValue, WriteDataValue};
            /// use std::io::Cursor;
            ///
            /// for byte in i8::MIN..=i8::MAX {
            ///     let value = DataValue::Byte(byte);
            ///     let mut writer = Vec::with_capacity(1);
            ///     writer.write_data_value(value).unwrap();
            ///     assert_eq!(&writer, &[byte as u8]);
            /// }
            /// for word in (i16::MIN..=i16::MAX).step_by(u16::MAX as usize / 257) {
            ///     let value = DataValue::Word(word);
            ///     let mut writer = Vec::with_capacity(2);
            ///     writer.write_data_value(value).unwrap();
            ///     assert_eq!(&writer, &word.to_le_bytes());
            /// }
            /// for longword in (i32::MIN..=i32::MAX).step_by(u32::MAX as usize / 251) {
            ///     let value = DataValue::Longword(longword);
            ///     let mut writer = Vec::with_capacity(2);
            ///     writer.write_data_value(value).unwrap();
            ///     assert_eq!(&writer, &longword.to_le_bytes());
            /// }
            /// ```
            fn write_data_value(&mut self, data_value: DataValue) -> Result<usize> {
                match data_value {
                    $(
                        DataValue::$desc(value) => {
                            let mut buf = [0; $count];
                            buf.copy_from_slice(&value.to_le_bytes());
                            self.write_all(&buf)?;
                            Ok($count)
                        }
                    )+
                }
            }
        }

        /// All types that implement `Write` get methods defined in `WriteDataValue` for free.
        impl<W: Write + ?Sized> WriteDataValue for W {}

        #[cfg(test)]
        pub(crate) mod data_value_tests {
            use super::*;
            use proptest::prelude::*;

            pub fn data_value_any() -> impl Strategy<Value = DataValue> {
                prop_oneof![
                    $(
                        any::<$out>().prop_map(DataValue::$desc),
                    )+
                ]
            }

            pub fn data_value(data_type: DataType) -> BoxedStrategy<DataValue> {
                match data_type {
                    $(
                        DataType::$desc => any::<$out>().prop_map(DataValue::$desc).boxed(),
                    )+
                }
            }
        }
    };
}

define_data_functions!{
    (Byte, 1, i8, "{}"),
    (Word, 2, i16, "{}"),
    (Longword, 4, i32, "{}"),
    (Quadword, 8, i64, "{}"),
    (Octoword, 16, i128, "{}"),
    (Floating, 4, FFloating, "{:e}"),
    (Double, 8, DFloating, "{:e}"),
    (GFloating, 8, GFloating, "{:e}"),
    (HFloating, 16, HFloating, "{:e}"),
}

macro_rules! operand_count {
    ($_: ident) => {1};
}

macro_rules! access_type {
    (ab) => {AccessType::Address};
    (aw) => {AccessType::Address};
    (al) => {AccessType::Address};
    (aq) => {AccessType::Address};
    (ao) => {AccessType::Address};
    (af) => {AccessType::Address};
    (ad) => {AccessType::Address};
    (ag) => {AccessType::Address};
    (ah) => {AccessType::Address};
    (bb) => {AccessType::Branch};
    (bw) => {AccessType::Branch};
    (bl) => {AccessType::Branch};
    (mb) => {AccessType::Modify};
    (mw) => {AccessType::Modify};
    (ml) => {AccessType::Modify};
    (mq) => {AccessType::Modify};
    (mo) => {AccessType::Modify};
    (mf) => {AccessType::Modify};
    (md) => {AccessType::Modify};
    (mg) => {AccessType::Modify};
    (mh) => {AccessType::Modify};
    (rb) => {AccessType::Read};
    (rw) => {AccessType::Read};
    (rl) => {AccessType::Read};
    (rq) => {AccessType::Read};
    (ro) => {AccessType::Read};
    (rf) => {AccessType::Read};
    (rd) => {AccessType::Read};
    (rg) => {AccessType::Read};
    (rh) => {AccessType::Read};
    (vb) => {AccessType::VariableBitField};
    (wb) => {AccessType::Write};
    (ww) => {AccessType::Write};
    (wl) => {AccessType::Write};
    (wq) => {AccessType::Write};
    (wo) => {AccessType::Write};
    (wf) => {AccessType::Write};
    (wd) => {AccessType::Write};
    (wg) => {AccessType::Write};
    (wh) => {AccessType::Write};
}

macro_rules! data_type {
    (ab) => {DataType::Byte};
    (aw) => {DataType::Word};
    (al) => {DataType::Longword};
    (aq) => {DataType::Quadword};
    (ao) => {DataType::Octoword};
    (af) => {DataType::Floating};
    (ad) => {DataType::Double};
    (ag) => {DataType::GFloating};
    (ah) => {DataType::HFloating};
    (bb) => {DataType::Byte};
    (bw) => {DataType::Word};
    (bl) => {DataType::Longword};
    (mb) => {DataType::Byte};
    (mw) => {DataType::Word};
    (ml) => {DataType::Longword};
    (mq) => {DataType::Quadword};
    (mo) => {DataType::Octoword};
    (mf) => {DataType::Floating};
    (md) => {DataType::Double};
    (mg) => {DataType::GFloating};
    (mh) => {DataType::HFloating};
    (rb) => {DataType::Byte};
    (rw) => {DataType::Word};
    (rl) => {DataType::Longword};
    (rq) => {DataType::Quadword};
    (ro) => {DataType::Octoword};
    (rf) => {DataType::Floating};
    (rd) => {DataType::Double};
    (rg) => {DataType::GFloating};
    (rh) => {DataType::HFloating};
    (vb) => {DataType::Byte};
    (wb) => {DataType::Byte};
    (ww) => {DataType::Word};
    (wl) => {DataType::Longword};
    (wq) => {DataType::Quadword};
    (wo) => {DataType::Octoword};
    (wf) => {DataType::Floating};
    (wd) => {DataType::Double};
    (wg) => {DataType::GFloating};
    (wh) => {DataType::HFloating};
}

macro_rules! count_operands {
    (()) => {0};
    (($n1:ident.$s1:ident)) => {1};
    (($n1:ident.$s1:ident, $n2:ident.$s2:ident, $n3:ident.$s3:ident, $n4:ident.$s4:ident, $n5:ident.$s5:ident, $n6:ident.$s6:ident)) => {6};
    (($($_:ident.$spec: ident),+)) => {
        (0 $( + operand_count!($spec) )+)
    };
}

macro_rules! commafy {
    ($s1: expr,) => { $s1 };
    ($s1: expr, $($s2: expr,)+) => { concat!($s1, $(", ", $s2,)+) };
}

macro_rules! operands_string {
    (()) => {""};
    (($($name:ident.$spec: ident),+)) => {
        commafy!(
        $(
            concat!(stringify!($name), ".", stringify!($spec)),
        )+
        )
    };
}

macro_rules! operands_slice {
    (()) => {&[]};
    (($($_:ident.$spec: ident),+)) => {&[
        $(
            (access_type!($spec), data_type!($spec)),
        )+
    ]};
}

#[allow(unused_macros)]  // Prevent it from whining about this test only macro.
macro_rules! instruction_prop_compose {
     ($word: literal, $opcode: ident, ()) => {
         any::<bool>().prop_map(|_| {
            let buf: Vec<u8> = if $word < 0x100 {
                vec![$word as u8]
            }
            else {
                ($word as u16).to_le_bytes().to_vec()
            };
            (Instruction::$opcode([]), buf)
        })
     };
     ($word: literal, $opcode: ident, ($($name: ident.$spec: ident),+)) => {
         ($(operand(access_type!($spec), data_type!($spec)),)+).prop_map(|($($name,)+)| {
            let mut buf = Vec::new();
            if $word < 0x100 {
                buf.push(($word & 0xFF) as u8);
            }
            else {
                buf.extend_from_slice(&($word as u16).to_le_bytes());
            }
            $(
                buf.extend_from_slice(&$name.1);
            )+
            (Instruction::$opcode([$($name.0,)+]), buf)
        })
    };
}

macro_rules! process_opcodes {
    (opcodes: {$(($word: expr, $opcode: ident, $operands: tt, $desc: expr),)*},
     duplicates: {$(($dup_word: expr, $dup_opcode: ident, $dup_operands: tt, $dup_desc: expr),)*}) => {
        /// # VAX Opcode
        #[derive(Copy, Clone, Debug, PartialEq, Eq)]
        #[repr(u16)]
        pub enum Opcode {
            $(
                #[doc = $desc]
                ///
                #[doc = concat!("Opcode ", stringify!($opcode), " = ", stringify!($word))]
                $opcode,
            )*
            $(
                #[doc = $dup_desc]
                ///
                #[doc = concat!("Opcode ", stringify!($dup_opcode), " = ", stringify!($dup_word))]
                $dup_opcode,
            )*
        }

        impl Opcode {
            /// Return a reference to an array with the access type and data type of the operands
            /// for a specific opcode.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::opcode::{AccessType, DataType, Opcode};
            ///
            /// assert_eq!(Opcode::HALT.operand_specs().len(), 0);
            /// assert_eq!(Opcode::HALT.operand_specs(), &[]);
            /// assert_eq!(Opcode::BRB.operand_specs().len(), 1);
            /// assert_eq!(Opcode::BRB.operand_specs(), &[(AccessType::Branch, DataType::Byte)]);
            /// assert_eq!(Opcode::MOVC5.operand_specs().len(), 5);
            /// assert_eq!(Opcode::MOVC5.operand_specs(), &[
            ///     (AccessType::Read, DataType::Word),
            ///     (AccessType::Address, DataType::Byte),
            ///     (AccessType::Read, DataType::Byte),
            ///     (AccessType::Read, DataType::Word),
            ///     (AccessType::Address, DataType::Byte),
            /// ]);
            /// ```
            pub const fn operand_specs(&self) -> &[(AccessType, DataType)] {
                use Opcode::*;
                match self {
                    $(
                        $opcode => operands_slice!($operands),
                    )*
                    $(
                        $dup_opcode => operands_slice!($dup_operands),
                    )*
                }
            }

            /// The size in bytes of the Opcode.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::opcode::Opcode;
            ///
            /// assert_eq!(Opcode::NOP.len(), 1);
            /// assert_eq!(Opcode::BPT.len(), 1);
            /// assert_eq!(Opcode::CLRQ.len(), 1);
            /// assert_eq!(Opcode::CLRD.len(), 1);
            /// assert_eq!(Opcode::CLRO.len(), 2);
            /// assert_eq!(Opcode::CLRH.len(), 2);
            /// ```
            pub const fn len(&self) -> usize {
                use Opcode::*;
                match self {
                    $(
                        $opcode => { if $word < 0x100 { 1 } else { 2 } }
                    )*
                    $(
                        $dup_opcode => { if $dup_word < 0x100 { 1 } else { 2 } }
                    )*
                }
            }

            /// Internal function used by Display to place the number of spaces after the opcode.
            const fn tab(&self) -> &'static str {
                use Opcode::*;
                const SPACES: [&'static str; 8] = [
                    "        ", "       ", "      ", "     ", "    ", "   ", "  ", " ",
                ];
                match self {
                    $(
                        $opcode => SPACES[stringify!($opcode).len()],
                    )+
                    $(
                        $dup_opcode => SPACES[stringify!($dup_opcode).len()],
                    )+
                }

            }
        }

        impl TryFrom<u16> for Opcode {
            type Error = Error;

            /// Convert from a u16 value into the corresponding `Opcode`.
            ///
            /// The majority of MACRO32 opcodes are one-byte opcodes, and the u8 value as a u16
            /// will translate into that opcode. If the first byte is 0xFD, 0xFE, or 0xFF, then it
            /// is a two-byte opcode. In those cases, the little-endian interpretation of the two
            /// byte is used for the conversion (i.e. [0xFD, 0x7C] (the CLRO opcode) is 0x7CFD).
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::opcode::{Opcode};
            /// use std::convert::TryFrom;
            ///
            /// assert_eq!(Opcode::try_from(1).unwrap(), Opcode::NOP);
            /// assert_eq!(Opcode::try_from(3).unwrap(), Opcode::BPT);
            /// assert_eq!(Opcode::try_from(0x7c).unwrap(), Opcode::CLRQ);
            /// assert_eq!(Opcode::try_from(0x7cfd).unwrap(), Opcode::CLRO);
            /// ```
            fn try_from(value: u16) -> Result<Self> {
                use $crate::opcode::Opcode::*;
                match value {
                    $(
                        $word => Ok($opcode),
                    )*
                    other => Err(Error::InvalidOpcode(other))
                }
            }
        }

        impl From<&Opcode> for u16 {
            /// Convert from a `Opcode` reference into the corresponding u16 value.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::opcode::{Opcode};
            /// use std::convert::TryFrom;
            ///
            /// assert_eq!(u16::from(&Opcode::NOP), 1);
            /// assert_eq!(u16::from(&Opcode::BPT), 3);
            /// assert_eq!(u16::from(&Opcode::CLRQ), 0x7c);
            /// assert_eq!(u16::from(&Opcode::CLRD), 0x7c);
            /// assert_eq!(u16::from(&Opcode::CLRO), 0x7cfd);
            /// assert_eq!(u16::from(&Opcode::CLRH), 0x7cfd);
            /// ```
            fn from(opcode: &Opcode) -> Self {
                match opcode {
                    $(
                        Opcode::$opcode => $word,
                    )+
                    $(
                        Opcode::$dup_opcode => $dup_word,
                    )+
                }
            }
        }

        impl From<Opcode> for u16 {
            /// Convert from a `Opcode` reference into the corresponding u16 value.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::opcode::{Opcode};
            /// use std::convert::TryFrom;
            ///
            /// assert_eq!(u16::from(Opcode::NOP), 1);
            /// assert_eq!(u16::from(Opcode::BPT), 3);
            /// assert_eq!(u16::from(Opcode::CLRQ), 0x7c);
            /// assert_eq!(u16::from(Opcode::CLRD), 0x7c);
            /// assert_eq!(u16::from(Opcode::CLRO), 0x7cfd);
            /// assert_eq!(u16::from(Opcode::CLRH), 0x7cfd);
            /// ```
            fn from(opcode: Opcode) -> Self {
                match opcode {
                    $(
                        Opcode::$opcode => $word,
                    )+
                    $(
                        Opcode::$dup_opcode => $dup_word,
                    )+
                }
            }
        }

        impl Display for Opcode {
            /// Formats the value using the given formatter.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::opcode::{Instruction, Opcode};
            /// use vax_disassembler::operand::{Operand, Register};
            ///
            ///
            /// assert_eq!(&format!("{}", Opcode::NOP), "NOP");
            /// assert_eq!(&format!("{}", Opcode::MOVC5) , "MOVC5");
            /// assert_eq!(&format!("{}", Opcode::PUSHAW) , "PUSHAW");
            /// assert_eq!(&format!("{}", Opcode::CVTFB) , "CVTFB");
            /// assert_eq!(&format!("{}", Opcode::INSQUE) , "INSQUE");
            /// ```
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                use Opcode::*;
                match self {
                    $(
                        $opcode => f.write_str(stringify!($opcode)),
                    )+
                    $(
                        $dup_opcode => f.write_str(stringify!($dup_opcode)),
                    )+
                }
            }
        }

        /// # VAX Instruction
        ///
        /// The VAX architecture has a variable-length instruction format. An instruction specifies
        /// an operation and 0 to 6 operands. An operand specifier determines how an operand is
        /// accessed. An operand specifier consists of an addressing mode specifier and, if needed,
        /// a specifier extension, immediate data, or an address.
        ///
        /// ## Examples
        ///
        /// ```rust
        /// use vax_disassembler::{
        ///     Instruction,
        ///     Operand,
        ///     ReadMacro32,
        ///     operand::Register,
        /// };
        /// use std::io::Cursor;
        ///
        /// let movc5_buf = [0x2C, 0x50, 0x61, 0x20, 0x52, 0x63];
        /// let instruction = Cursor::new(movc5_buf).disassemble().unwrap();
        /// assert_eq!(instruction, Instruction::MOVC5([
        ///     Operand::Register(Register::R0),
        ///     Operand::RegisterDeferred(Register::R1),
        ///     Operand::Literal(0x20),
        ///     Operand::Register(Register::R2),
        ///     Operand::RegisterDeferred(Register::R3),
        /// ]));
        /// assert_eq!(&format!("{}", instruction), "MOVC5   R0, (R1), S^#32, R2, (R3)");
        /// ```
        #[derive(Copy, Clone, Debug, PartialEq, Eq)]
        pub enum Instruction {
            $(
                #[doc = $desc]
                ///
                #[doc = concat!("Format: ", stringify!($opcode), "   ", operands_string!($operands))]
                $opcode([Operand; count_operands!($operands)]),
            )*
            $(
                /// ## Format:
                #[doc = concat!("`opcode\t", operands_string!($dup_operands), "`")]
                ///
                /// ## Opcode:
                #[doc = concat!("`", stringify!($dup_word), "\t", stringify!($dup_opcode), "\t", $dup_desc, "`")]
                $dup_opcode([Operand; count_operands!($dup_operands)]),
            )*
        }

        impl Instruction {
            /// Return the [`Opcode`] for this `Instruction`.
            ///
            /// # Examples
            /// ```rust
            /// use vax_disassembler::opcode::{Instruction, Opcode};
            /// use vax_disassembler::operand::{Operand, Register};
            ///
            /// assert_eq!(Instruction::RSB([]).opcode(), Opcode::RSB);
            /// assert_eq!(Instruction::TSTL([Operand::Register(Register::R0)]).opcode(), Opcode::TSTL);
            /// ```
            pub fn opcode(&self) -> Opcode {
                match self {
                    $(
                        Instruction::$opcode(_) => Opcode::$opcode,
                    )+
                    $(
                        Instruction::$dup_opcode(_) => Opcode::$dup_opcode,
                    )+
                }
            }

            /// Return a slice with all of the operands for this instruction.
            ///
            /// # Examples
            /// ```rust
            /// use vax_disassembler::opcode::{Instruction, Opcode};
            /// use vax_disassembler::operand::{Operand, Register};
            ///
            /// // MOVC5 R0, (R1), S^#^A/ /, R2, (R3)
            /// let instruction = Instruction::MOVC5([
            ///     Operand::Register(Register::R0),
            ///     Operand::RegisterDeferred(Register::R1),
            ///     Operand::Literal(b' '),
            ///     Operand::Register(Register::R2),
            ///     Operand::RegisterDeferred(Register::R3),
            /// ]);
            ///
            /// let mut operands = instruction.operands().iter();
            /// assert_eq!(operands.next().unwrap(), &Operand::Register(Register::R0));
            /// assert_eq!(operands.next().unwrap(), &Operand::RegisterDeferred(Register::R1));
            /// assert_eq!(operands.next().unwrap(), &Operand::Literal(b' '));
            /// assert_eq!(operands.next().unwrap(), &Operand::Register(Register::R2));
            /// assert_eq!(operands.next().unwrap(), &Operand::RegisterDeferred(Register::R3));
            /// assert!(operands.next().is_none());
            /// ```
            pub fn operands(&self) -> &[Operand] {
                match self {
                    $(
                        Instruction::$opcode(ref slice) => slice,
                    )+
                    $(
                        Instruction::$dup_opcode(ref slice) => slice,
                    )+
                }
            }

            pub(crate) fn operands_mut(&mut self) -> &mut [Operand] {
                match self {
                    $(
                        Instruction::$opcode(ref mut slice) => slice,
                    )+
                    $(
                        Instruction::$dup_opcode(ref mut slice) => slice,
                    )+
                }
            }
        }

        impl From<Opcode> for Instruction {
            fn from(opcode: Opcode) -> Self {
                match opcode {
                    $(
                        Opcode::$opcode => Instruction::$opcode([Operand::Undefined; count_operands!($operands)]),
                    )+
                    $(
                        Opcode::$dup_opcode => Instruction::$dup_opcode([Operand::Undefined; count_operands!($dup_operands)]),
                    )+
                }
            }
        }

        impl Display for Instruction {
            /// Formats the value using the given formatter.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use vax_disassembler::opcode::{Instruction, Opcode};
            /// use vax_disassembler::operand::{Operand, Register};
            ///
            /// assert_eq!(&format!("{}", Instruction::NOP([])), "NOP");
            /// assert_eq!(
            ///     &format!("{}", Instruction::MOVC5([
            ///         Operand::Register(Register::R0),
            ///         Operand::RegisterDeferred(Register::R1),
            ///         Operand::Literal(b' '),
            ///         Operand::Register(Register::R2),
            ///         Operand::RegisterDeferred(Register::R3),
            ///     ])),
            ///     "MOVC5   R0, (R1), S^#32, R2, (R3)"
            /// );
            /// ```
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                let opcode = self.opcode();
                write!(f, "{:?}", opcode)?;
                let mut comma = opcode.tab();
                for operand in self.operands() {
                    write!(f, "{}{}", comma, operand)?;
                    comma = ", ";
                }
                Ok(())
            }
        }

        #[cfg(test)]
        mod opcode_tests {
            use super::*;
            use crate::operand::tests::operand;
            use proptest::prelude::*;

            /// This generates a random instruction. It doesn't include the duplicate instructions.
            pub fn instruction() -> impl Strategy<Value = (Instruction, Vec<u8>)> {
                prop_oneof![$(
                    instruction_prop_compose!($word, $opcode, $operands),
                )*]
            }

            /// This generates a random instruction, including the duplicate instructions.
            ///
            /// When decoding the buffer, duplicate instructions will not be generated, so don't
            /// use this for ReadMacro32 tests.
            pub fn instruction_w_dup() -> impl Strategy<Value = (Instruction, Vec<u8>)> {
                prop_oneof![
                $(
                    instruction_prop_compose!($word, $opcode, $operands),
                )*
                $(
                    instruction_prop_compose!($dup_word, $dup_opcode, $dup_operands),
                )*
                ]
            }

            #[test]
            fn verify_u16_to_opcode() {
                $(
                    assert_eq!(Opcode::try_from($word).unwrap(), Opcode::$opcode);
                )*
            }

            #[test]
            fn verify_duplicate_opcodes() {
                $(
                    let opcode_u16 = u16::from(&Opcode::$dup_opcode);
                    if (opcode_u16 < 0x100) || ((opcode_u16 & 0xFF) >= 0xFD) {
                        assert_ne!(Opcode::$dup_opcode, Opcode::try_from(opcode_u16).unwrap());
                    }
                )+
            }
        }
    };
}

// This calls the process_opcodes with the VAX opcode list.
include!("process_opcodes.in");

impl Instruction {
    /// Length of the [Instruction] in bytes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use vax_disassembler::opcode::Instruction;
    /// use vax_disassembler::operand::{IndexedOperand, Operand, Register};
    ///
    /// assert_eq!(Instruction::NOP([]).len(), 1);
    /// assert_eq!(Instruction::BPT([]).len(), 1);
    /// assert_eq!(Instruction::CLRQ([Operand::Indexed(
    ///     IndexedOperand::LongwordDisplacement(-123456, Register::R0), Register::R1)]).len(), 7);
    /// assert_eq!(Instruction::CLRO([Operand::Indexed(
    ///     IndexedOperand::LongwordDisplacement(7654321, Register::R2), Register::R3)]).len(), 8);
    /// ```
    pub fn len(&self) -> usize {
        let mut len = self.opcode().len();
        for operand in self.operands().iter() {
            len += operand.len();
        }
        len
    }
}

#[cfg(test)]
mod tests {
    use super::opcode_tests::{instruction, instruction_w_dup};
    use proptest::prelude::*;
    use crate::{ReadMacro32, WriteInstruction};

    proptest! {
        #[test]
        fn verify_read_instruction((instruction, buf) in instruction()) {
            let mut reader = std::io::Cursor::new(buf);
            assert_eq!(instruction, reader.disassemble().unwrap());
        }
    }

    proptest! {
        #[test]
        fn verify_write_instruction((instruction, expected) in instruction()) {
            let mut buf = Vec::new();
            buf.write_instruction(instruction)?;
            assert_eq!(&buf, &expected);
        }
    }

    proptest! {
        #[test]
        #[ignore]
        // This isn't a test. It is to manually verify that instruction() is working properly.
        fn print_instruction((instruction, _buf) in instruction_w_dup()) {
            static mut FIRST_TIME: bool = true;
            if unsafe { FIRST_TIME } {
                use std::{thread::sleep, time::Duration};
                // Wait for other tests to finish. . .
                sleep(Duration::from_millis(100));
                unsafe { FIRST_TIME = false; }
            }
            println!("{}", instruction);
        }
    }
}
