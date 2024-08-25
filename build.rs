use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

fn main() {
    generate_u16_map();
    generate_name_map();
}

macro_rules! process_opcodes {
    (opcodes: {$(($word: expr, $opcode: ident, $operands: tt, $desc: expr),)*},
     duplicates: {$(($dup_word: expr, $dup_opcode: ident, $dup_operands: tt, $dup_desc: expr),)*}) => {
        fn generate_u16_map() {
            let path = Path::new(&env::var("OUT_DIR").unwrap()).join("word_map.rs");
            let mut file = BufWriter::new(File::create(&path).unwrap());

            write!(
                &mut file,
                "static WORD_TO_OPCODE: phf::Map<u16, Opcode> = {}",
                phf_codegen::Map::new()
                $(
                    .entry($word, concat!("Opcode::", stringify!($opcode)))
                )+
                    .build()
            )
            .unwrap();
            write!(&mut file, ";\n").unwrap();
        }

        fn generate_name_map() {
            let path = Path::new(&env::var("OUT_DIR").unwrap()).join("name_map.rs");
            let mut file = BufWriter::new(File::create(&path).unwrap());

            write!(
                &mut file,
                "static NAME_TO_OPCODE: phf::Map<&'static str, Opcode> = {}",
                phf_codegen::Map::new()
                $(
                    .entry(stringify!($opcode), concat!("Opcode::", stringify!($opcode)))
                )+
                $(
                    .entry(stringify!($dup_opcode), concat!("Opcode::", stringify!($dup_opcode)))
                )+
                    .build()
            )
            .unwrap();
            write!(&mut file, ";\n").unwrap();
        }
    };
}

include!("src/process_opcodes.in");
