use vax_disassembler::opcode::Opcode;

macro_rules! process_opcodes {
    (opcodes: {$(($word: expr, $opcode: ident, $operands: tt, $desc: expr),)*},
     duplicates: {$(($dup_word: expr, $dup_opcode: ident, $dup_operands: tt, $dup_desc: expr),)*}) => {
        #[allow(dead_code)]
        const OPCODE: &[Opcode] = &[
            $(
                Opcode::$opcode,
            )*
        ];

        #[test]
        fn test_opcode_u16_lookup() {
            $(
            let from_u16 = Opcode::try_from($word as u16).unwrap();
            assert_eq!(from_u16, Opcode::$opcode);
            )*
        }

        #[test]
        fn test_u16_opcode_lookup() {
            $(
            let to_u16 = u16::from(Opcode::$opcode);
            assert_eq!(to_u16, $word);
            )*
            $(
            let to_u16 = u16::from(Opcode::$dup_opcode);
            assert_eq!(to_u16, $dup_word);
            )*
        }

        #[test]
        fn test_opcode_len_lookup() {
            $(
            let len = if 256_u16 > $word { 1 } else { 2 };
            assert_eq!(len, Opcode::$opcode.len());
            )*
            $(
            let len = if 256_u16 > $dup_word { 1 } else { 2 };
            assert_eq!(len, Opcode::$dup_opcode.len());
            )*
        }
    };
}

include!("../src/process_opcodes.in");
