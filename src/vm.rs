use crate::data;
use crate::data::{Data, Pointer, SizeT};
use crate::float::FloatPoint;
use crate::heap::Heap;
use std::io;

// ByteCode Virtual Machine ///////////////////////////////////////////////////
//
// Struct for a simple byte code virtual machine. Is constructed with a Heap
// and run on a program rather than constructed with one.
//
// Should be as simple as possible, except for some convinience operations where
// simple would multiply the number of ops needed in assembled code. The other
// places it cannot be too simple are I/O, File Ops, and Memory Management. If the
// vm does not do these things the program has no way to access them.
//
// The other sticky spot that might add some ops is whether an op takes its args
// from the program or the stack. Many memory ops can take everything from the
// program as it should be known at compile time, except the heap. Everything
// else should use the stack, but if something is used a lot both ways
// can add a second one that takes pc or stack.
//
// The main goal is that the vm has no concept of what your program should look
// like. I.e. we added static memory loads and copies, but the vm has no idea that
// we will put static data at the program start and jump it to start operations.
//
//
// TODOS //////////////////////////////////////////////////////////////////////
//
// TODO Fix i/o ops and find a way to test them properly.
// TODO make a map for file pointers, maybe a separate structure like the heap.
// Something that can hold a bunch of them with pointers like the heap. All operations
// for files will take a file pointer and use this strucutre.
// TODO make sure panics/expects are done in a way that the programmer gets a
// reasonable message about what happened. I.e. we don't want these to be segfaults.
// Even though corrupted programs end up in wierd states.

#[derive(Debug)]
pub struct ByteVm<T: Heap, R: io::Read, W: io::Write> {
    pc: usize,
    sp: usize,
    rsp: usize,
    stack: Vec<Data>,
    return_stack: Vec<Data>,
    heap: T,
    input: R,
    output: W,
}

impl<T: Heap> ByteVm<T, io::Stdin, io::Stdout> {
    pub fn new(heap: T) -> ByteVm<T, io::Stdin, io::Stdout> {
        ByteVm::new_with_io(heap, io::stdin(), io::stdout())
    }
}

impl<T: Heap, R: io::Read, W: io::Write> ByteVm<T, R, W> {
    pub fn new_with_io(heap: T, input: R, output: W) -> ByteVm<T, R, W> {
        ByteVm {
            pc: 0,
            sp: 0,
            rsp: 0,
            stack: Vec::with_capacity(1024),
            return_stack: Vec::with_capacity(512),
            heap: heap,
            input: input,
            output: output,
        }
    }

    pub fn reset(&mut self) {
        self.pc = 0;
        self.sp = 0;
        self.rsp = 0;
        self.stack.clear();
        self.return_stack.clear();
        self.heap.free_all();
    }

    // Stack Operations ///////////////////////////////////////////////////////
    //
    // Because the sp and rsp start at 0 they will always point 1 past the top.
    // Any stack access related to the top should use these methods.

    // Adding and removing elements
    fn pop(&mut self, amount: usize) {
        let size = self.stack.len().saturating_sub(amount);
        self.stack.truncate(size);
        self.sp = self.sp.saturating_sub(amount);
    }

    fn push(&mut self, val: Data) {
        self.stack.push(val);
        self.sp += 1;
    }

    fn rpop(&mut self, amount: usize) {
        let size = self.return_stack.len().saturating_sub(amount);
        self.return_stack.truncate(size);
        self.rsp = self.rsp.saturating_sub(amount);
    }

    fn rpush(&mut self, val: Data) {
        self.return_stack.push(val);
        self.rsp += 1;
    }

    // Accessing and setting elements
    fn top(&self) -> Data {
        self.stack[self.sp - 1]
    }

    fn from_top(&self, offset: usize) -> Data {
        self.stack[self.sp - 1 - offset]
    }

    fn at(&self, idx: usize) -> Data {
        self.stack[idx]
    }

    fn set_top(&mut self, val: Data) {
        self.stack[self.sp - 1] = val;
    }

    fn set_from_top(&mut self, offset: usize, val: Data) {
        self.stack[self.sp - 1 - offset] = val;
    }

    fn set_at(&mut self, idx: usize, val: Data) {
        self.stack[idx] = val;
    }

    fn rtop(&self) -> Data {
        self.return_stack[self.rsp - 1]
    }

    fn data_to_chars(&self, slice: &[Data]) -> Vec<u8> {
        // This seems inefficient
        let mut bytes = Vec::new();
        for int in slice.iter() {
            for b in int.to_be_bytes().iter() {
                if *b == 0 {
                    continue;
                } else {
                    bytes.push(b.clone());
                }
            }
        }
        return bytes;
    }

    // Program Exectuion //////////////////////////////////////////////////////

    pub fn run(&mut self, program: &[Data]) {
        self.reset();
        let mut running = true;
        let mut inc_pc = true;
        while running && self.pc < program.len() {
            let op = program[self.pc];
            // Match op
            match op {
                data::HALT => running = false,

                // Stack //

                // value is from pc
                data::PUSH => {
                    self.pc += 1;
                    self.push(program[self.pc]);
                }
                data::POP => {
                    self.pop(1);
                }
                // location is from pc
                data::LOAD => {
                    self.pc += 1;
                    let loc = program[self.pc] as usize;
                    let val = self.at(loc);
                    self.push(val);
                }
                // location is from pc
                data::STORE => {
                    self.pc += 1;
                    let loc = program[self.pc] as usize;
                    self.set_at(loc, self.top());
                    self.pop(1);
                }
                // location is from pc
                data::STATIC => {
                    self.pc += 1;
                    let loc = program[self.pc] as usize;
                    self.push(program[loc]);
                }
                data::FIRST => {
                    self.push(self.top());
                }
                data::SECOND => {
                    self.push(self.from_top(1));
                }
                data::THIRD => {
                    self.push(self.from_top(2));
                }
                data::NTH => {
                    self.pc += 1;
                    let offset = program[self.pc] as usize;
                    self.push(self.from_top(offset));
                }
                data::SWAP => {
                    let fst = self.top();
                    self.set_top(self.from_top(1));
                    self.set_from_top(1, fst);
                }
                data::ROTATE => {
                    let last = self.from_top(2);
                    self.set_from_top(2, self.from_top(1));
                    self.set_from_top(1, self.top());
                    self.set_top(last);
                }
                // add static load

                // Return Stack
                data::RPUSH => {
                    self.rpush(self.top());
                    self.pop(1);
                }
                data::RPOP => {
                    self.push(self.rtop());
                    self.rpop(1);
                }
                data::RPEEK => {
                    self.push(self.rtop());
                }

                // Heap memory
                // Since these should be fully dynamic in number and location
                // they take all arguments off of the stack.
                data::ALLOC => {
                    let p = self.heap.alloc(self.top() as SizeT);
                    // will large pointers, that are u32 go negative properly?
                    self.set_top(p as Data);
                }
                data::FREE => {
                    self.heap.free(self.top() as Pointer);
                    self.pop(1);
                }
                data::HLOAD => {
                    let pointer = self.top() as Pointer;
                    self.set_top(self.heap.get(pointer, 0));
                }
                data::HSTORE => {
                    let val = self.top();
                    let pointer = self.from_top(1) as Pointer;
                    self.heap.set(pointer, 0, val);
                    self.pop(2);
                }
                data::HGETAT => {
                    let offset = self.top() as SizeT;
                    let pointer = self.from_top(1) as Pointer;
                    self.set_from_top(1, self.heap.get(pointer, offset));
                    self.pop(1);
                }
                data::HSETAT => {
                    let val = self.top();
                    let offset = self.from_top(1) as SizeT;
                    let pointer = self.from_top(2) as Pointer;
                    self.heap.set(pointer, offset, val);
                    self.pop(3);
                }

                // Arithmetic
                data::ADD => {
                    let a = self.from_top(1);
                    self.set_from_top(1, a.wrapping_add(self.top()));
                    self.pop(1);
                }
                data::SUBTRACT => {
                    let a = self.from_top(1);
                    self.set_from_top(1, a.wrapping_sub(self.top()));
                    self.pop(1);
                }
                data::MULTIPLY => {
                    let a = self.from_top(1);
                    self.set_from_top(1, a.wrapping_mul(self.top()));
                    self.pop(1);
                }
                data::QUOTIENT => {
                    let a = self.from_top(1);
                    self.set_from_top(1, a / self.top());
                    self.pop(1);
                }
                data::REMAINDER => {
                    let a = self.from_top(1);
                    self.set_from_top(1, a % self.top());
                    self.pop(1);
                }
                data::MODULO => {
                    let a = self.from_top(1);
                    let b = self.top();
                    self.set_from_top(1, ((a % b) + b) % b);
                    self.pop(1);
                }

                // Logic
                data::EQUAL => {
                    let a = self.from_top(1);
                    self.set_from_top(1, (a == self.top()) as i32);
                    self.pop(1);
                }
                data::LESS => {
                    let a = self.from_top(1);
                    self.set_from_top(1, (a < self.top()) as i32);
                    self.pop(1);
                }
                data::GREATER => {
                    let a = self.from_top(1);
                    self.set_from_top(1, (a > self.top()) as i32);
                    self.pop(1);
                }
                data::LESSEQ => {
                    let a = self.from_top(1);
                    self.set_from_top(1, (a <= self.top()) as i32);
                    self.pop(1);
                }
                data::GREATEREQ => {
                    let a = self.from_top(1);
                    self.set_from_top(1, (a >= self.top()) as i32);
                    self.pop(1);
                }
                data::LOGICNOT => {
                    let a = self.top();
                    if a == 0 {
                        self.set_top(1);
                    } else {
                        self.set_top(0);
                    }
                }
                data::LOGICAND => {
                    let a = self.top();
                    let b = self.from_top(1);
                    self.pop(1);
                    if a != 0 && b != 0 {
                        self.set_top(1);
                    } else {
                        self.set_top(0);
                    }
                }
                data::LOGICOR => {
                    let a = self.top();
                    let b = self.from_top(1);
                    self.pop(1);
                    if a != 0 || b != 0 {
                        self.set_top(1);
                    } else {
                        self.set_top(0);
                    }
                }

                // Control Flow
                // These only accept pc arguments
                data::JUMP => {
                    self.pc += 1;
                    self.pc = program[self.pc] as usize;
                    inc_pc = false;
                }
                data::BRANCH => {
                    self.pc += 1;
                    if self.top() != 0 {
                        self.pc = program[self.pc] as usize;
                        inc_pc = false;
                    }
                    self.pop(1);
                }
                data::CALL => {
                    self.rpush((self.pc + 2) as i32);
                    self.pc += 1;
                    self.pc = program[self.pc] as usize;
                    inc_pc = false;
                }
                data::RETURN => {
                    self.push(self.rtop());
                    self.rpop(1);
                    self.pc = self.top() as usize;
                    self.pop(1);
                    inc_pc = false;
                }

                // Bits
                data::LSHIFT => {
                    self.set_from_top(1, self.from_top(1) << self.top());
                    self.pop(1);
                }
                data::RSHIFT => {
                    self.set_from_top(1, self.from_top(1) >> self.top());
                    self.pop(1);
                }
                data::BITNOT => {
                    self.set_top(!self.top());
                }
                data::BITAND => {
                    self.set_from_top(1, self.from_top(1) & self.top());
                    self.pop(1);
                }
                data::BITOR => {
                    self.set_from_top(1, self.from_top(1) | self.top());
                    self.pop(1);
                }
                data::BITXOR => {
                    self.set_from_top(1, self.from_top(1) ^ self.top());
                    self.pop(1);
                }

                // I/O
                // readline straight to heap, via a string buffer, return the
                // pointer and size
                data::READLINE => {
                    let mut buffer = String::new();
                    self.input
                        .read_to_string(&mut buffer)
                        .expect("failed to read line (READLINE)");
                    let string = buffer
                        .strip_suffix("\r\n")
                        .or(buffer.strip_suffix("\n"))
                        .unwrap_or(&buffer);
                    let mut vec = Vec::new();
                    for ch in string.chars() {
                        vec.push(ch as Data);
                    }
                    let size = vec.len() as Data;
                    let pointer = self.heap.add_block(vec);
                    self.push(pointer as Data);
                    self.push(size);
                }
                // read onto the stack
                data::READINT => {
                    let mut buffer = String::new();
                    self.input
                        .read_to_string(&mut buffer)
                        .expect("failed to read line (READINT)");
                    let x: i32 = buffer.trim().parse().expect("input should be a valid INT");
                    self.push(x);
                }
                // Write a char to out
                data::WRITECHAR => {
                    let ch = self.top();
                    let mut bytes = Vec::new();
                    for b in ch.to_be_bytes().iter() {
                        if *b == 0 {
                            continue;
                        } else {
                            bytes.push(b.clone());
                        }
                    }
                    self.output
                        .write(&bytes)
                        .expect("unable to write char to output stream");
                    self.pop(1);
                }
                // Write an int to out
                data::WRITEINT => {
                    let int = self.top();
                    write!(self.output, "{}", int).expect("unable to write INT to output stream");
                    self.pop(1);
                }
                // write a static range
                data::WRITESTATIC => {
                    let start = program[self.pc + 1] as usize;
                    let amt = program[self.pc + 2] as usize;
                    let slc = &program[start..(start + amt)];
                    let bytes = self.data_to_chars(slc);
                    self.output
                        .write(&bytes)
                        .expect("unable to write static chars to output stream");
                    self.pc += 2;
                }
                // write a range on stack, no popping
                data::WRITESTACK => {
                    let start = program[self.pc + 1] as usize;
                    let amt = program[self.pc + 2] as usize;
                    let slc = &self.stack[start..(start + amt)];
                    let bytes = self.data_to_chars(slc);
                    self.output
                        .write(&bytes)
                        .expect("unable to write stack chars to output stream");
                    self.pc += 2;
                }
                // write a range from a heap block
                data::WRITEHEAP => {
                    let heap_ptr = self.top() as Pointer;
                    let offset = program[self.pc + 1] as SizeT;
                    let amt = program[self.pc + 2] as SizeT;
                    let slc = &self.heap.get_slice(heap_ptr, offset, amt);
                    let bytes = self.data_to_chars(slc);
                    self.output
                        .write(&bytes)
                        .expect("unable to write static chars to output stream");
                    self.pop(1);
                    self.pc += 2;
                }

                // Memory
                // These only accept pc arguments
                // NOTE there is no checking to ensure these actually copy to valid
                // memory locations
                data::PUSHN => {
                    let start = self.pc + 2;
                    let amt = program[self.pc + 1] as usize;
                    let end = start + amt;
                    let slc = &program[start..end];
                    self.stack.extend(slc);
                    self.sp += amt;
                    self.pc = end;
                    inc_pc = false;
                }
                data::POPN => {
                    self.pc += 1;
                    self.pop(program[self.pc] as usize);
                }
                data::STACKALLOC => {
                    self.pc += 1;
                    let amt = program[self.pc] as usize;
                    self.stack.resize(self.stack.len() + amt, 0);
                    self.sp += amt;
                }
                data::STACKCOPY => {
                    let start_idx = program[self.pc + 1] as usize;
                    let dest_idx = program[self.pc + 2] as usize;
                    let amt = program[self.pc + 3] as usize;
                    self.stack
                        .copy_within(start_idx..(start_idx + amt), dest_idx);
                    self.pc += 3;
                }
                data::STATICTOSTACK => {
                    let start_idx = program[self.pc + 1] as usize;
                    let dest_idx = program[self.pc + 2] as usize;
                    let amt = program[self.pc + 3] as usize;
                    let prog_slc = &program[start_idx..(start_idx + amt)];
                    self.stack[dest_idx..(dest_idx + amt)].copy_from_slice(prog_slc);
                    self.pc += 3;
                }
                data::STATICTOHEAP => {
                    let heap_pointer = self.top() as Pointer;
                    let start_idx = program[self.pc + 1] as usize;
                    let heap_offset = program[self.pc + 2] as usize;
                    let amt = program[self.pc + 3] as usize;
                    let prog_slc = &program[start_idx..(start_idx + amt)];
                    self.heap
                        .get_mut_slice(heap_pointer, heap_offset as SizeT, amt as SizeT)
                        .copy_from_slice(prog_slc);
                    self.pop(1);
                    self.pc += 3;
                }
                data::STACKTOHEAP => {
                    let heap_pointer = self.top() as Pointer;
                    let start_idx = program[self.pc + 1] as usize;
                    let heap_offset = program[self.pc + 2] as usize;
                    let amt = program[self.pc + 3] as usize;
                    let stack_slc = &self.stack[start_idx..(start_idx + amt)];
                    self.heap
                        .get_mut_slice(heap_pointer, heap_offset as SizeT, amt as SizeT)
                        .copy_from_slice(stack_slc);
                    self.pop(1);
                    self.pc += 3;
                }
                data::HEAPTOSTACK => {
                    let heap_pointer = self.top() as Pointer;
                    let heap_offset = program[self.pc + 1] as usize;
                    let dest_idx = program[self.pc + 2] as usize;
                    let amt = program[self.pc + 3] as usize;
                    let heap_slc =
                        self.heap
                            .get_slice(heap_pointer, heap_offset as SizeT, amt as SizeT);
                    self.stack[dest_idx..(dest_idx + amt)].copy_from_slice(heap_slc);
                    self.pop(1);
                    self.pc += 3;
                }
                // No copy from heap to heap because borrowing both vecs at the same
                // time is not possible for me. So I would just have to copy anyway
                // and it is just about as easy for a copy to and from stack with
                // the above operations

                // Floating Point
                // Definately inefficient. Could be faster if I could use the memory
                // on the stack directly as an f64 rather than converting back and forth.
                // But I have no idea how to do it, or do it in a portable way.
                // However, this way we are using rusts built in float and all of
                // the speed and precision that comes with it. Better than implementing
                // my own float type.
                data::INTTOFLOAT => {
                    let i = self.top();
                    let f = FloatPoint::new(i as f64);
                    self.set_top(f.upper);
                    self.push(f.lower);
                }
                data::FLOATTOINT => {
                    let f = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    self.pop(2);
                    self.push(f.float as Data);
                }
                data::FLOATADD => {
                    let a = FloatPoint::from_data(self.from_top(3), self.from_top(2));
                    let b = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    let res = FloatPoint::new(a.float + b.float);
                    self.set_from_top(3, res.upper);
                    self.set_from_top(2, res.lower);
                    self.pop(2);
                }
                data::FLOATSUB => {
                    let a = FloatPoint::from_data(self.from_top(3), self.from_top(2));
                    let b = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    let res = FloatPoint::new(a.float - b.float);
                    self.set_from_top(3, res.upper);
                    self.set_from_top(2, res.lower);
                    self.pop(2);
                }
                data::FLOATMULT => {
                    let a = FloatPoint::from_data(self.from_top(3), self.from_top(2));
                    let b = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    let res = FloatPoint::new(a.float * b.float);
                    self.set_from_top(3, res.upper);
                    self.set_from_top(2, res.lower);
                    self.pop(2);
                }
                data::FLOATDIV => {
                    let a = FloatPoint::from_data(self.from_top(3), self.from_top(2));
                    let b = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    let res = FloatPoint::new(a.float / b.float);
                    self.set_from_top(3, res.upper);
                    self.set_from_top(2, res.lower);
                    self.pop(2);
                }
                data::FLOATEQ => {
                    let a = FloatPoint::from_data(self.from_top(3), self.from_top(2));
                    let b = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    self.pop(3);
                    self.set_top((a.float == b.float) as Data);
                }
                data::FLOATLESS => {
                    let a = FloatPoint::from_data(self.from_top(3), self.from_top(2));
                    let b = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    self.pop(3);
                    self.set_top((a.float < b.float) as Data);
                }
                data::FLOATGREAT => {
                    let a = FloatPoint::from_data(self.from_top(3), self.from_top(2));
                    let b = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    self.pop(3);
                    self.set_top((a.float > b.float) as Data);
                }
                data::FLOATLEQ => {
                    let a = FloatPoint::from_data(self.from_top(3), self.from_top(2));
                    let b = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    self.pop(3);
                    self.set_top((a.float <= b.float) as Data);
                }
                data::FLOATGEQ => {
                    let a = FloatPoint::from_data(self.from_top(3), self.from_top(2));
                    let b = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    self.pop(3);
                    self.set_top((a.float >= b.float) as Data);
                }
                data::READFLOAT => {
                    let mut buffer = String::new();
                    self.input
                        .read_to_string(&mut buffer)
                        .expect("failed to read line (READFLOAT)");
                    let x: f64 = buffer
                        .trim()
                        .parse()
                        .expect("input should be a valid FLOAT");
                    let res = FloatPoint::new(x);
                    self.push(res.upper);
                    self.push(res.lower);
                }
                data::WRITEFLOAT => {
                    let f = FloatPoint::from_data(self.from_top(1), self.from_top(0));
                    write!(self.output, "{}", f.to_string())
                        .expect("unable to write FLOAT to output stream");
                    self.pop(2);
                }

                // File Operations
                // add later

                // Bad OpCode
                _ => {
                    panic!("Bad OpCode")
                }
            }

            // Set next op
            if inc_pc {
                self.pc += 1;
            }
            inc_pc = true;
        }

        // Clean up if needed
    }
}

// Tests //////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod vm_tests {
    use super::*;
    use crate::heap::HashHeap;

    // RUN testing with actual programs ///////////////////////////////////////

    fn setup_vm() -> ByteVm<HashHeap, io::Stdin, io::Stdout> {
        let heap = HashHeap::new();
        ByteVm::new(heap)
    }

    // BASIC STACK OPCODES //

    #[test]
    fn test_push() {
        let mut vm = setup_vm();
        vm.run(&vec![data::PUSH, 10, data::HALT]);
        assert_eq!(vec![10], vm.stack);
        assert_eq!(vm.sp, 1);
    }

    #[test]
    fn test_pop() {
        let mut vm = setup_vm();
        vm.run(&vec![data::PUSH, 10, data::PUSH, 20, data::POP, data::HALT]);
        assert_eq!(vec![10], vm.stack);
        assert_eq!(vm.sp, 1);
    }

    #[test]
    fn test_load() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            20,
            data::LOAD,
            0,
            data::HALT,
        ]);
        assert_eq!(vec![10, 20, 10], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    #[test]
    fn test_store() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            10,
            data::PUSH,
            20,
            data::STORE,
            0,
            data::HALT,
        ]);
        assert_eq!(vec![20, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_static() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::JUMP,
            5,
            33,
            45,
            65,
            data::STATIC,
            4,
            data::STATIC,
            3,
            data::STATIC,
            2,
            data::HALT,
        ]);
        assert_eq!(vec![65, 45, 33], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    #[test]
    fn test_first() {
        let mut vm = setup_vm();
        vm.run(&vec![data::PUSH, 10, data::FIRST, data::HALT]);
        assert_eq!(vec![10, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_second() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            20,
            data::SECOND,
            data::HALT,
        ]);
        assert_eq!(vec![10, 20, 10], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    #[test]
    fn test_third() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            20,
            data::PUSH,
            30,
            data::THIRD,
            data::HALT,
        ]);
        assert_eq!(vec![10, 20, 30, 10], vm.stack);
        assert_eq!(vm.sp, 4);
    }

    #[test]
    fn test_nth() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            20,
            data::PUSH,
            30,
            data::NTH,
            1,
            data::HALT,
        ]);
        assert_eq!(vec![10, 20, 30, 20], vm.stack);
        assert_eq!(vm.sp, 4);
    }

    #[test]
    fn test_swap() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            20,
            data::SWAP,
            data::HALT,
        ]);
        assert_eq!(vec![20, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_rotate() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            20,
            data::PUSH,
            30,
            data::ROTATE,
            data::HALT,
        ]);
        assert_eq!(vec![20, 30, 10], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    // RETURN STACK OPCODES //

    #[test]
    fn test_rpush() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            20,
            data::RPUSH,
            data::HALT,
        ]);
        assert_eq!(vec![10], vm.stack);
        assert_eq!(vec![20], vm.return_stack);
        assert_eq!(vm.sp, 1);
        assert_eq!(vm.rsp, 1);
    }

    #[test]
    fn test_rpop() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            20,
            data::RPUSH,
            data::RPUSH,
            data::RPOP,
            data::HALT,
        ]);
        assert_eq!(vec![10], vm.stack);
        assert_eq!(vec![20], vm.return_stack);
        assert_eq!(vm.sp, 1);
        assert_eq!(vm.rsp, 1);
    }

    #[test]
    fn test_rpeek() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            20,
            data::RPUSH,
            data::RPUSH,
            data::RPEEK,
            data::HALT,
        ]);
        assert_eq!(vec![10], vm.stack);
        assert_eq!(vec![20, 10], vm.return_stack);
        assert_eq!(vm.sp, 1);
        assert_eq!(vm.rsp, 2);
    }

    // HEAP OPCODES //
    // These tests are coupled to the HashHeap implementation
    #[test]
    fn test_heap_alloc() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::ALLOC,
            data::PUSH,
            13,
            data::ALLOC,
            data::HALT,
        ]);
        assert_eq!(vm.sp, 2);
        assert_eq!(vm.heap.size(), 18);
    }

    #[test]
    fn test_heap_free() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::ALLOC,
            data::PUSH,
            13,
            data::ALLOC,
            data::FREE,
            data::HALT,
        ]);
        assert_eq!(vm.sp, 1);
        assert_eq!(vm.heap.size(), 5);
    }

    #[test]
    fn test_heap_store() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::ALLOC,
            data::PUSH,
            13,
            data::ALLOC,
            data::PUSH,
            45,
            data::HSTORE,
            data::HALT,
        ]);
        assert_eq!(vm.sp, 1);
        // assumes heap pointers start from 0
        assert_eq!(vm.heap.get(1, 0), 45);
    }

    #[test]
    fn test_heap_load() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::ALLOC,
            data::PUSH,
            13,
            data::ALLOC,
            data::FIRST,
            data::PUSH,
            45,
            data::HSTORE,
            data::HLOAD,
            data::HALT,
        ]);
        // assumes heap pointers start at 0
        assert_eq!(vec![0, 45], vm.stack);
    }

    #[test]
    fn test_heap_set_at() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::ALLOC,
            data::PUSH,
            13,
            data::ALLOC,
            data::PUSH,
            3,
            data::PUSH,
            45,
            data::HSETAT,
            data::HALT,
        ]);
        assert_eq!(vm.sp, 1);
        // assumes heap pointers start at 0
        assert_eq!(vm.heap.get(1, 3), 45);
    }

    #[test]
    fn test_heap_get_at() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::ALLOC,
            data::PUSH,
            13,
            data::ALLOC,
            data::FIRST,
            data::PUSH,
            3,
            data::PUSH,
            45,
            data::HSETAT,
            data::PUSH,
            3,
            data::HGETAT,
            data::HALT,
        ]);
        assert_eq!(vec![0, 45], vm.stack);
    }

    // ARITHMETIC OPCODES //
    #[test]
    fn test_add() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            7,
            data::ADD,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![12, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_subtract() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            7,
            data::SUBTRACT,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![-2, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_multiply() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            7,
            data::MULTIPLY,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![35, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_multiply_overflow() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            i32::MAX - 1,
            data::PUSH,
            i32::MAX,
            data::MULTIPLY,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![-2147483646, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_quotient_even() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            5,
            data::QUOTIENT,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![2, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_quotient_truncated() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            3,
            data::QUOTIENT,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![3, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_quotient_big_denom() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            300,
            data::QUOTIENT,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![0, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_quotient_negatives() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            -3,
            data::QUOTIENT,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![-3, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    #[should_panic]
    fn test_quotient_div_0() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            0,
            data::QUOTIENT,
            data::PUSH,
            10,
            data::HALT,
        ]);
    }

    #[test]
    fn test_remainder() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            3,
            data::REMAINDER,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![1, 10], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_negative_remainders() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            10,
            data::PUSH,
            -3,
            data::REMAINDER,
            data::PUSH,
            -10,
            data::PUSH,
            3,
            data::REMAINDER,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![1, -1, 10], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    #[test]
    fn test_modulus() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            -21,
            data::PUSH,
            4,
            data::REMAINDER,
            data::PUSH,
            -21,
            data::PUSH,
            4,
            data::MODULO,
            data::PUSH,
            10,
            data::HALT,
        ]);
        assert_eq!(vec![-1, 3, 10], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    // LOGIC OPCODES //
    #[test]
    fn test_equal() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            5,
            data::EQUAL,
            data::PUSH,
            8,
            data::PUSH,
            -7,
            data::EQUAL,
            data::HALT,
        ]);
        assert_eq!(vec![1, 0], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_less() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            5,
            data::LESS,
            data::PUSH,
            8,
            data::PUSH,
            -7,
            data::LESS,
            data::PUSH,
            -8,
            data::PUSH,
            -7,
            data::LESS,
            data::HALT,
        ]);
        assert_eq!(vec![0, 0, 1], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    #[test]
    fn test_greater() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            5,
            data::GREATER,
            data::PUSH,
            8,
            data::PUSH,
            -7,
            data::GREATER,
            data::PUSH,
            -8,
            data::PUSH,
            -7,
            data::GREATER,
            data::HALT,
        ]);
        assert_eq!(vec![0, 1, 0], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    #[test]
    fn test_less_equal() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            5,
            data::LESSEQ,
            data::PUSH,
            8,
            data::PUSH,
            -7,
            data::LESSEQ,
            data::PUSH,
            -8,
            data::PUSH,
            -7,
            data::LESSEQ,
            data::HALT,
        ]);
        assert_eq!(vec![1, 0, 1], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    #[test]
    fn test_greater_equal() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            5,
            data::GREATEREQ,
            data::PUSH,
            8,
            data::PUSH,
            -7,
            data::GREATEREQ,
            data::PUSH,
            -8,
            data::PUSH,
            -7,
            data::GREATEREQ,
            data::HALT,
        ]);
        assert_eq!(vec![1, 1, 0], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    #[test]
    fn test_logic_not() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::LOGICNOT,
            data::PUSH,
            0,
            data::LOGICNOT,
            data::HALT,
        ]);
        assert_eq!(vec![0, 1], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_logic_and() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            0,
            data::LOGICAND,
            data::PUSH,
            0,
            data::PUSH,
            0,
            data::LOGICAND,
            data::PUSH,
            1,
            data::PUSH,
            -1,
            data::LOGICAND,
            data::HALT,
        ]);
        assert_eq!(vec![0, 0, 1], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    #[test]
    fn test_logic_or() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            0,
            data::LOGICOR,
            data::PUSH,
            0,
            data::PUSH,
            0,
            data::LOGICOR,
            data::PUSH,
            1,
            data::PUSH,
            -1,
            data::LOGICOR,
            data::HALT,
        ]);
        assert_eq!(vec![1, 0, 1], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    // CONTROL FLOW OPCODES //
    #[test]
    fn test_jump() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::JUMP,
            5,
            data::HALT,
            data::PUSH,
            13,
            data::HALT,
        ]);
        assert_eq!(vec![5, 13], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_branch_true() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            5,
            data::EQUAL,
            data::BRANCH,
            8,
            data::HALT,
            data::PUSH,
            13,
            data::HALT,
        ]);
        assert_eq!(vec![13], vm.stack);
        assert_eq!(vm.sp, 1);
    }

    #[test]
    fn test_branch_false() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            7,
            data::EQUAL,
            data::BRANCH,
            10,
            data::PUSH,
            99,
            data::HALT,
            data::PUSH,
            13,
            data::HALT,
        ]);
        assert_eq!(vec![99], vm.stack);
        assert_eq!(vm.sp, 1);
    }

    #[test]
    fn test_call_and_return() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::PUSH,
            7,
            data::CALL, // jump to 9 and put 6 on rstack
            9,
            data::PUSH,
            99,
            data::HALT,
            data::PUSH, // procedure at 9
            13,
            data::RETURN, // jump back to 6
        ]);
        assert_eq!(vec![5, 7, 13, 99], vm.stack);
        assert_eq!(vm.sp, 4);
    }

    // BITWISE OPCODES //
    #[test]
    fn test_left_shift() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            1,
            data::PUSH,
            2,
            data::LSHIFT,
            data::PUSH,
            i32::MAX,
            data::PUSH,
            1,
            data::LSHIFT,
            data::HALT,
        ]);
        assert_eq!(vec![4, -2], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_right_shift() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            16,
            data::PUSH,
            2,
            data::RSHIFT,
            data::PUSH,
            -2,
            data::PUSH,
            1,
            data::RSHIFT,
            data::HALT,
        ]);
        assert_eq!(vec![4, -1], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_bit_not() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            -2,
            data::BITNOT,
            data::PUSH,
            0,
            data::BITNOT,
            data::PUSH,
            1,
            data::BITNOT,
            data::HALT,
        ]);
        assert_eq!(vec![1, -1, -2], vm.stack);
        assert_eq!(vm.sp, 3);
    }

    #[test]
    fn test_and() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            7,
            data::PUSH,
            3,
            data::BITAND,
            data::PUSH,
            i32::MAX,
            data::BITAND,
            data::HALT,
        ]);
        assert_eq!(vec![3], vm.stack);
        assert_eq!(vm.sp, 1);
    }

    #[test]
    fn test_or() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            1,
            data::PUSH,
            2,
            data::BITOR,
            data::PUSH,
            8,
            data::BITOR,
            data::HALT,
        ]);
        assert_eq!(vec![11], vm.stack);
        assert_eq!(vm.sp, 1);
    }

    #[test]
    fn test_xor() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            1,
            data::PUSH,
            2,
            data::BITXOR,
            data::PUSH,
            7,
            data::BITXOR,
            data::HALT,
        ]);
        assert_eq!(vec![4], vm.stack);
        assert_eq!(vm.sp, 1);
    }

    // MEMORY OPCODES //
    #[test]
    fn test_push_n_values() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSHN,
            5,
            1,
            2,
            3,
            4,
            5,
            data::PUSH, // check to make sure the pc updates correctly
            345,
            data::HALT,
        ]);
        assert_eq!(vec![1, 2, 3, 4, 5, 345], vm.stack);
        assert_eq!(vm.sp, 6);
    }

    #[test]
    fn test_pop_n_values() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSHN,
            5,
            1,
            2,
            3,
            4,
            5,
            data::POPN,
            3,
            data::HALT,
        ]);
        assert_eq!(vec![1, 2], vm.stack);
        assert_eq!(vm.sp, 2);
    }

    #[test]
    fn test_stack_alloc() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            5,
            data::STACKALLOC,
            3,
            data::PUSH,
            99,
            data::HALT,
        ]);
        assert_eq!(vec![5, 0, 0, 0, 99], vm.stack);
        assert_eq!(vm.sp, 5);
    }

    #[test]
    fn test_stack_copy() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSHN,
            3,
            1,
            2,
            3,
            data::PUSH,
            99,
            data::STACKALLOC,
            3,
            data::STACKCOPY,
            0,
            4,
            2,
            data::PUSH,
            99,
            data::HALT,
        ]);
        assert_eq!(vec![1, 2, 3, 99, 1, 2, 0, 99], vm.stack);
        assert_eq!(vm.sp, 8);
    }

    #[test]
    fn test_static_to_stack_copy() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::JUMP,
            5,
            45,
            87,
            99,
            data::STACKALLOC,
            3,
            data::STATICTOSTACK,
            2,
            0,
            3,
            data::PUSH,
            -12,
            data::HALT,
        ]);
        assert_eq!(vec![45, 87, 99, -12], vm.stack);
        assert_eq!(vm.sp, 4);
    }

    #[test]
    fn test_static_to_heap_copy() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::JUMP,
            5,
            45,
            87,
            99,
            data::PUSH,
            5,
            data::ALLOC,
            data::STATICTOHEAP,
            2,
            2,
            3,
            data::PUSH,
            -12,
            data::HALT,
        ]);
        assert_eq!(vec![-12], vm.stack);
        assert_eq!(vm.sp, 1);
        // assumes heap pointers start at 0
        assert_eq!(vm.heap.get(0, 2), 45);
        assert_eq!(vm.heap.get(0, 3), 87);
        assert_eq!(vm.heap.get(0, 4), 99);
    }

    #[test]
    fn test_stack_to_heap_copy() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            45,
            data::PUSH,
            87,
            data::PUSH,
            99,
            data::PUSH,
            5,
            data::ALLOC,
            data::STACKTOHEAP,
            0,
            2,
            3,
            data::PUSH,
            -12,
            data::HALT,
        ]);
        assert_eq!(vec![45, 87, 99, -12], vm.stack);
        assert_eq!(vm.sp, 4);
        // assumes heap pointers start at 0
        assert_eq!(vm.heap.get(0, 2), 45);
        assert_eq!(vm.heap.get(0, 3), 87);
        assert_eq!(vm.heap.get(0, 4), 99);
    }

    #[test]
    fn test_heap_to_stack_copy() {
        let mut vm = setup_vm();
        vm.run(&vec![
            // setup heap
            data::PUSH,
            5,
            data::ALLOC,
            data::FIRST,
            data::PUSH,
            2,
            data::PUSH,
            45,
            data::HSETAT,
            data::FIRST,
            data::PUSH,
            3,
            data::PUSH,
            87,
            data::HSETAT,
            data::FIRST,
            data::PUSH,
            4,
            data::PUSH,
            99,
            data::HSETAT,
            // pointer still on stack
            // alloc on stack and copy
            data::RPUSH,
            data::STACKALLOC,
            3,
            data::RPOP,
            data::HEAPTOSTACK,
            2,
            0,
            3,
            // ensure pc in right place
            data::PUSH,
            -12,
            data::HALT,
        ]);
        assert_eq!(vec![45, 87, 99, -12], vm.stack);
        assert_eq!(vm.sp, 4);
        // assumes heap pointers start at 0
        assert_eq!(vm.heap.get(0, 2), 45);
        assert_eq!(vm.heap.get(0, 3), 87);
        assert_eq!(vm.heap.get(0, 4), 99);
    }

    // READ/WRITE OPERATIONS
    // Uses different i/o
    #[test]
    fn test_write_top_of_stack_as_bytes() {
        let expect = "H".as_bytes();
        let input = "".as_bytes();
        let mut out: Vec<u8> = vec![0; expect.len()];
        let mut vm = ByteVm::new_with_io(HashHeap::new(), input, &mut out[0..]);
        vm.run(&vec![data::PUSH, 'H' as Data, data::WRITECHAR, data::HALT]);
        assert_eq!(out, expect);
    }

    #[test]
    fn test_write_top_of_stack_as_int() {
        let expect = "123456789".as_bytes();
        let input = "".as_bytes();
        let mut out: Vec<u8> = vec![0; expect.len()];
        let mut vm = ByteVm::new_with_io(HashHeap::new(), input, &mut out[0..]);
        vm.run(&vec![data::PUSH, 123456789, data::WRITEINT, data::HALT]);
        assert_eq!(out, expect);
    }

    #[test]
    fn test_stack_range_as_bytes() {
        let expect = "1234".as_bytes();
        let input = "".as_bytes();
        let mut out: Vec<u8> = vec![0; expect.len()];
        let mut vm = ByteVm::new_with_io(HashHeap::new(), input, &mut out[0..]);
        vm.run(&vec![
            data::PUSHN,
            4,
            49,
            50,
            51,
            52,
            data::WRITESTACK,
            0,
            4,
            data::PUSH,
            99,
            data::HALT,
        ]);
        assert_eq!(vm.stack, vec![49, 50, 51, 52, 99]); // must check first because borrowing out
        assert_eq!(out, expect);
    }

    #[test]
    fn test_static_range_as_bytes() {
        let expect = "1234".as_bytes();
        let input = "".as_bytes();
        let mut out: Vec<u8> = vec![0; expect.len()];
        let mut vm = ByteVm::new_with_io(HashHeap::new(), input, &mut out[0..]);
        vm.run(&vec![
            data::JUMP,
            6,
            49,
            50,
            51,
            52,
            data::WRITESTATIC,
            2,
            4,
            data::PUSH,
            99,
            data::HALT,
        ]);
        assert_eq!(vm.stack, vec![99]);
        assert_eq!(out, expect);
    }

    #[test]
    fn test_heap_range_as_bytes() {
        let expect = "1234".as_bytes();
        let input = "".as_bytes();
        let mut out: Vec<u8> = vec![0; expect.len()];
        let mut vm = ByteVm::new_with_io(HashHeap::new(), input, &mut out[0..]);
        vm.run(&vec![
            data::JUMP,
            6,
            49,
            50,
            51,
            52,
            data::PUSH,
            4,
            data::ALLOC,
            data::FIRST,
            data::STATICTOHEAP,
            2,
            0,
            4,
            data::WRITEHEAP,
            0,
            4,
            data::PUSH,
            -12,
            data::HALT,
        ]);
        assert_eq!(vm.stack, vec![-12]);
        assert_eq!(out, expect);
    }

    #[test]
    fn test_read_int_onto_stack() {
        let input = "-123456789\n".as_bytes();
        let mut out: Vec<u8> = Vec::new();
        let mut vm = ByteVm::new_with_io(HashHeap::new(), input, &mut out[0..]);
        vm.run(&vec![data::READINT, data::HALT]);
        assert_eq!(vm.top(), -123456789);
    }

    #[test]
    fn test_read_line_onto_stack() {
        let input = "hello\n".as_bytes();
        let mut out: Vec<u8> = Vec::new();
        let mut vm = ByteVm::new_with_io(HashHeap::new(), input, &mut out);
        vm.run(&vec![data::READLINE, data::HALT]);
        assert_eq!(vm.stack, vec![0, 5]);
        assert_eq!(vm.heap.get_slice(0, 0, 5), vec![104, 101, 108, 108, 111]);
    }

    // FLOATING POINT OPS
    #[test]
    fn test_float_add() {
        let mut vm = setup_vm();
        vm.run(&vec![
            data::PUSH,
            1083394629,
            data::PUSH,
            -2059935035,
            data::SECOND,
            data::SECOND,
            data::FLOATADD,
            data::PUSH,
            99,
            data::HALT,
        ]);
        assert_eq!(vm.stack, vec![1084443205, -2059935035, 99]);
    }
}
