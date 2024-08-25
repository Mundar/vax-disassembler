use vax_disassembler::opcode::Opcode;

macro_rules! process_opcodes {
    (opcodes: {$(($word: expr, $opcode: ident, $operands: tt, $desc: expr),)*},
     duplicates: {$(($dup_word: expr, $dup_opcode: ident, $dup_operands: tt, $dup_desc: expr),)*}) => {
        #[test]
        fn test_opcode_u16_lookup() {
            $(
            let from_u16 = Opcode::try_from($word as u16).unwrap();
            assert_eq!(from_u16, Opcode::$opcode);
            )*
        }
    };
}

include!("../src/process_opcodes.in");
