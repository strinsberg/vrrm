// Data types and constants

// Type aliases for readability ///////////////////////////////////////////////
pub type Data = i32;
pub type Pointer = u32;
pub type OpCode = i32;
pub type SizeT = u32;

// Opcodes ////////////////////////////////////////////////////////////////////

// Wanted to use enum, but the conversions were not nice in a match statement
// and seemed like they would cause the match to either not be a fast switch
// or would add unsafe or extra conversions to each code step. Since the
// Assembler will use this lib it can use the constants to create the codes and
// they will not get out of date, but some gross function will probably be needed
// for debugging

pub const HALT: OpCode = 0;
// Stack
pub const PUSH: OpCode = 1;
pub const POP: OpCode = 2;
pub const LOAD: OpCode = 3;
pub const STORE: OpCode = 4;
pub const FIRST: OpCode = 5;
pub const SECOND: OpCode = 6;
pub const THIRD: OpCode = 7;
pub const NTH: OpCode = 8;
pub const SWAP: OpCode = 9;
pub const ROTATE: OpCode = 10;
// Return Stack
pub const RPUSH: OpCode = 11;
pub const RPOP: OpCode = 12;
pub const RPEEK: OpCode = 13;
// Heap
pub const ALLOC: OpCode = 14;
pub const FREE: OpCode = 15;
pub const HLOAD: OpCode = 16;
pub const HSTORE: OpCode = 17;
pub const HGETAT: OpCode = 18;
pub const HSETAT: OpCode = 19;
// Arithmetic
pub const ADD: OpCode = 20;
pub const SUBTRACT: OpCode = 21;
pub const MULTIPLY: OpCode = 22;
pub const QUOTIENT: OpCode = 23;
pub const REMAINDER: OpCode = 24;
// Logic
pub const EQUAL: OpCode = 25;
pub const LESS: OpCode = 26;
pub const GREATER: OpCode = 27;
pub const LESSEQ: OpCode = 28;
pub const GREATEREQ: OpCode = 29;
// Control Flow
pub const JUMP: OpCode = 30;
pub const BRANCH: OpCode = 31;
pub const CALL: OpCode = 32;
pub const RETURN: OpCode = 33;
// Bits
pub const LSHIFT: OpCode = 34;
pub const RSHIFT: OpCode = 35;
pub const BITNOT: OpCode = 36;
pub const BITAND: OpCode = 37;
pub const BITOR: OpCode = 38;
pub const BITXOR: OpCode = 39;
// Bytes **unused**
pub const GETBYTE0: OpCode = 40;
pub const GETBYTE1: OpCode = 41;
pub const GETBYTE2: OpCode = 42;
pub const GETBYTE3: OpCode = 43;
pub const SETBYTE0: OpCode = 44;
pub const SETBYTE1: OpCode = 45;
pub const SETBYTE2: OpCode = 46;
pub const SETBYTE3: OpCode = 47;
pub const PACKBYTES: OpCode = 48;
pub const UNPACKBYTES: OpCode = 49;
// I/O
pub const READLINE: OpCode = 51;
pub const READINT: OpCode = 52;
pub const WRITECHAR: OpCode = 53;
pub const WRITEINT: OpCode = 54;
pub const WRITESTACK: OpCode = 55;
// Blocks
pub const PUSHN: OpCode = 56;
pub const POPN: OpCode = 57;
pub const STACKCOPY: OpCode = 58;
pub const STACKTOHEAPCOPY: OpCode = 59;
pub const HEAPTOSTACKCOPY: OpCode = 60;
pub const STACKALLOC: OpCode = 61;
// Floating Point
pub const INTTOFLOAT: OpCode = 62;
pub const FLOATTOINT: OpCode = 63;
pub const FLOATADD: OpCode = 64;
pub const FLOATSUB: OpCode = 65;
pub const FLOATMULT: OpCode = 66;
pub const FLOATDIV: OpCode = 67;
pub const FLOATEQ: OpCode = 68;
pub const FLOATLESS: OpCode = 69;
pub const FLOATGREAT: OpCode = 70;
pub const FLOATLEQ: OpCode = 71;
pub const FLOATGEQ: OpCode = 72;
pub const READFLOAT: OpCode = 73;
pub const WRITEFLOAT: OpCode = 74;
// File operations
//
// Missed
pub const MODULO: OpCode = 200;
pub const LOGICNOT: OpCode = 201;
pub const LOGICAND: OpCode = 202;
pub const LOGICOR: OpCode = 203;
pub const STATIC: OpCode = 204;
pub const STATICTOSTACK: OpCode = 205;
pub const STATICTOHEAP: OpCode = 206;
pub const STACKTOHEAP: OpCode = 207;
pub const HEAPTOSTACK: OpCode = 208;
pub const WRITESTATIC: OpCode = 209;
pub const WRITEHEAP: OpCode = 210;
