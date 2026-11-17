# Change Log

## [Unreleased]

## [0.2.0] - 2026-11-17

- Updated vax-floating crate to 0.2.1+ to get bug fixes for that crate.

## [0.1.2] - 2026-10-20

- Added len() functions to DataValue, Operand, Opcode, and Instruction types.
- Added `WriteInstruction`, `WriteOperand`, and `WriteDataValue` traits to extend the `std::io::Write` trait.

## [0.1.1] - 2024-08-25

### Fixed

- ReadMacro32 incorrectly labeled as reading to an Operand instead of an Instruction.
