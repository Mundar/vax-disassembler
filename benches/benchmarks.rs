use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::fmt::{self, Display, Formatter};
use vax_disassembler::{
    Error,
    Result,
    AccessType,
    DataType,
    Opcode as RealOpcode,
};

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

macro_rules! operands_slice {
    (()) => {&[]};
    (($($name:ident.$op_spec: ident),+)) => {&[
        $(
            (access_type!($op_spec), data_type!($op_spec)),
        )+
    ]};
}

include!(concat!(env!("OUT_DIR"), "/word_map.rs"));
include!(concat!(env!("OUT_DIR"), "/name_map.rs"));

macro_rules! process_opcodes {
    (opcodes: {$(($word: expr, $opcode: ident, $operands: tt, $desc: expr),)*},
     duplicates: {$(($org_opcode: expr, $dup_opcode: ident, $dup_operands: tt, $dup_desc: expr),)*}) => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq)]
        pub enum Opcode {
            $(
                $opcode,
            )*
            $(
                $dup_opcode,
            )*
        }

        impl Opcode {
            pub fn try_from_match(value: u16) -> Result<Self> {
                match value {
                    $(
                        $word => Ok(Opcode::$opcode),
                    )*
                    other => Err(Error::InvalidOpcode(other))
                }
            }

            pub fn try_from_phf(value: u16) -> Option<Self> {
                WORD_TO_OPCODE.get(&value).copied()
            }

            pub fn from_str_match(name: &str) -> Result<Self> {
                match name {
                    $(
                        stringify!($opcode) => Ok(Opcode::$opcode),
                    )*
                    $(
                        stringify!($dup_opcode) => Ok(Opcode::$dup_opcode),
                    )*
                    other => Err(Error::InvalidOpcodeString(other.to_string()))
                }
            }

            pub fn from_str_phf(name: &str) -> Option<Self> {
                NAME_TO_OPCODE.get(name).copied()
            }

            pub fn operands(&self) -> &[(AccessType, DataType)] {
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
        }

        impl Display for Opcode {
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
    };
}

include!("../src/process_opcodes.in");

fn bench_opcode(c: &mut Criterion) {
    let mut group = c.benchmark_group("Opcode");
    for i in [0_u16, 0xFC_u16, 0xFEFF_u16, 0x00FF_u16].iter() {
        group.bench_with_input(BenchmarkId::new("TryFrom match", i), i, 
            |b, i| b.iter(|| Opcode::try_from_match(*i)));
        group.bench_with_input(BenchmarkId::new("TryFrom phf", i), i, 
            |b, i| b.iter(|| Opcode::try_from_phf(*i)));
    }
    for i in ["HALT", "XFC", "BUGW", "BAD"].iter() {
        group.bench_with_input(BenchmarkId::new("FromStr match", i), i, 
            |b, i| b.iter(|| Opcode::from_str_match(i)));
        group.bench_with_input(BenchmarkId::new("FromStr phf", i), i, 
            |b, i| b.iter(|| Opcode::from_str_phf(i)));
    }
    for i in [Opcode::HALT, Opcode::XFC, Opcode::BUGW].iter() {
        group.bench_with_input(BenchmarkId::new("Bench Opcode operands", i), i, 
            |b, i| b.iter(|| i.operands()));
    }
    for i in [RealOpcode::HALT, RealOpcode::XFC, RealOpcode::BUGW].iter() {
        group.bench_with_input(BenchmarkId::new("Crate Opcode operands", i), i, 
            |b, i| b.iter(|| i.operand_specs()));
    }
    group.finish();
}

criterion_group!(benches, bench_opcode);
criterion_main!(benches);

