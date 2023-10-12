use crate::data::{Data, Pointer, SizeT};
use std::collections::HashMap;

// Heap Trait /////////////////////////////////////////////////////////////////

pub trait Heap {
    fn alloc(&mut self, size: SizeT) -> Pointer;
    fn free(&mut self, p: Pointer);
    fn get(&self, p: Pointer, offset: SizeT) -> Data;
    fn set(&mut self, p: Pointer, offset: SizeT, d: Data);
    fn free_all(&mut self);
    fn get_slice(&self, p: Pointer, offset: SizeT, amount: SizeT) -> &[Data];
    fn get_mut_slice(&mut self, p: Pointer, offset: SizeT, amount: SizeT) -> &mut [Data];
    fn size(&self) -> SizeT;
    fn block_size(&self, p: Pointer) -> SizeT;
    fn add_block(&mut self, b: Vec<Data>) -> Pointer;
    fn resize_block(&mut self, p: Pointer, new_size: SizeT, val: Data);
}

// Hash Heap Implementation ///////////////////////////////////////////////////

#[derive(Debug)]
pub struct HashHeap {
    idx: Pointer,
    pool: HashMap<SizeT, Vec<Vec<Data>>>,
    heap: HashMap<Pointer, Vec<Data>>,
}

impl HashHeap {
    pub fn new() -> HashHeap {
        HashHeap {
            idx: 0,
            pool: HashMap::new(),
            heap: HashMap::new(),
        }
    }

    fn update_idx(&mut self) {
        while self.heap.contains_key(&self.idx) {
            self.idx = self.idx.wrapping_add(1);
        }
    }
}

impl Heap for HashHeap {
    fn alloc(&mut self, size: SizeT) -> Pointer {
        let idx = self.idx;
        // reuse freed objects of size if available, otherwise allocate new ones
        if self.pool.contains_key(&size) && !self.pool[&size].is_empty() {
            let mem = self.pool.get_mut(&size).unwrap().pop().unwrap();
            self.heap.insert(idx, mem);
        } else {
            let mut mem = Vec::new();
            mem.resize(size as usize, 0);
            self.heap.insert(idx, mem);
        }
        // the idx should always be the next valid idx when we finish
        // in any method that allocs memory
        self.update_idx();
        return idx;
    }

    fn free(&mut self, p: Pointer) {
        // remove the memory from heap
        let mem = self
            .heap
            .remove(&p)
            .expect("pointer should be live in heap");
        // if there is a pool for this size push this one, otherwise make pool and push
        let size = mem.len() as SizeT;
        if self.pool.contains_key(&size) {
            self.pool.get_mut(&size).unwrap().push(mem);
        } else {
            self.pool.insert(size, vec![mem]);
        }
    }

    fn get(&self, p: Pointer, offset: SizeT) -> Data {
        *self
            .heap
            .get(&p)
            .expect("pointer should be live in heap")
            .get(offset as usize)
            .expect("offset should be in bounds")
    }

    fn set(&mut self, p: Pointer, offset: SizeT, d: Data) {
        *self
            .heap
            .get_mut(&p)
            .expect("pointer should be live in heap")
            .get_mut(offset as usize)
            .expect("offset should be in bounds") = d;
    }

    fn free_all(&mut self) {
        // could still move memory to pool instead of just removing it
        // loop self.heap.keys and call self.free on each key, i.e. the pointers
        self.heap.clear();
    }

    fn get_slice(&self, p: Pointer, offset: SizeT, amount: SizeT) -> &[Data] {
        &self.heap[&p][offset as usize..(offset + amount) as usize]
    }

    fn get_mut_slice(&mut self, p: Pointer, offset: SizeT, amount: SizeT) -> &mut [Data] {
        &mut self
            .heap
            .get_mut(&p)
            .expect("pointer should be live in heap")[offset as usize..(offset + amount) as usize]
    }

    fn size(&self) -> SizeT {
        let s: usize = self.heap.iter().map(|(_, v)| v.len()).sum();
        return s as SizeT;
    }

    fn block_size(&self, p: Pointer) -> SizeT {
        self.heap
            .get(&p)
            .expect("pointer should be live in heap")
            .len() as SizeT
    }

    fn add_block(&mut self, b: Vec<Data>) -> Pointer {
        let idx = self.idx;
        self.heap.insert(idx, b);
        self.update_idx();
        return idx;
    }

    fn resize_block(&mut self, p: Pointer, new_size: SizeT, val: Data) {
        self.heap
            .get_mut(&p)
            .expect("pointer should be live in heap")
            .resize(new_size as usize, val);
    }
}

// Tests //////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod vm_tests {
    use super::*;

    #[test]
    fn test_alloc_new_mem() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10);
        assert_eq!(p, 0);
        assert_eq!(hp.idx, 1);
        assert_eq!(hp.heap[&p].len(), 10);

        let p2 = hp.alloc(5);
        assert_eq!(p2, 1);
        assert_eq!(hp.idx, 2);
        assert_eq!(hp.heap[&p2].len(), 5);
    }

    #[test]
    fn test_alloc_big_mem() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10_000_000);
        assert_eq!(p, 0);
        assert_eq!(hp.idx, 1);
        assert_eq!(hp.heap[&p].len(), 10_000_000);
    }

    #[test]
    fn test_free_mem() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10);
        assert_eq!(p, 0);
        assert_eq!(hp.heap[&p].len(), 10);
        assert_eq!(hp.pool.contains_key(&10), false);

        hp.free(p);
        assert_eq!(hp.heap.contains_key(&p), false);
        assert_eq!(hp.pool[&10].len(), 1);
        assert_eq!(hp.pool[&10][0].len(), 10);
    }

    #[test]
    fn test_free_when_mem_pool_is_initialized_for_mem_size() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10);
        let p2 = hp.alloc(10);
        hp.free(p);
        hp.free(p2);
        assert_eq!(hp.heap.contains_key(&p), false);
        assert_eq!(hp.heap.contains_key(&p2), false);
        assert_eq!(hp.pool[&10].len(), 2);
        assert_eq!(hp.pool[&10][0].len(), 10);
        assert_eq!(hp.pool[&10][1].len(), 10);
    }

    #[test]
    #[should_panic]
    fn test_free_mem_bad_pointer() {
        let mut hp = HashHeap::new();
        hp.free(35);
    }

    #[test]
    fn test_alloc_reuse_pool_mem() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10);
        hp.free(p);
        let p2 = hp.alloc(10);
        assert_eq!(p2, 1);
        assert_eq!(hp.idx, 2);
        assert_eq!(hp.heap[&p2].len(), 10);
        assert_eq!(hp.pool[&10].len(), 0);
    }

    #[test]
    fn test_get() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10);
        hp.heap.get_mut(&p).unwrap()[5] = 33;
        // currently no guarantee is made that mem is always zeroed.
        // It will be when it is newly allocated but not when reused from pool
        // assert_eq!(hp.get(p, 0), 0);
        assert_eq!(hp.get(p, 5), 33);
    }

    #[test]
    #[should_panic]
    fn test_get_bad_pointer() {
        let hp = HashHeap::new();
        hp.get(97, 0);
    }

    #[test]
    #[should_panic]
    fn test_get_bad_offset() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10);
        hp.get(p, 99);
    }

    #[test]
    fn test_set() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10);
        hp.set(p, 0, 42);
        hp.set(p, 3, 163);
        assert_eq!(hp.get(p, 0), 42);
        assert_eq!(hp.get(p, 3), 163);
    }

    #[test]
    #[should_panic]
    fn test_set_bad_pointer() {
        let mut hp = HashHeap::new();
        hp.set(97, 0, 13);
    }

    #[test]
    #[should_panic]
    fn test_set_bad_offset() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10);
        hp.set(p, 17, 44);
    }

    #[test]
    fn test_free_all() {
        let mut hp = HashHeap::new();
        hp.alloc(10);
        hp.alloc(5);
        hp.alloc(20);
        hp.alloc(5);
        assert_eq!(hp.heap.len(), 4);
        hp.free_all();
        assert_eq!(hp.heap.len(), 0);
        // currently the pool is not used in this case
        // easy way would be to iterate hp.heap.keys in heap (the used pointers)
        // and free them each with hp.free
        assert_eq!(hp.pool.len(), 0);
    }

    #[test]
    fn test_get_total_alloced_mem_size() {
        let mut hp = HashHeap::new();
        hp.alloc(10);
        hp.alloc(5);
        hp.alloc(20);
        hp.alloc(5);
        assert_eq!(hp.size(), 40);
    }

    #[test]
    fn test_get_alloced_mesize_for_block() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10);
        assert_eq!(hp.block_size(p), 10);
    }

    #[test]
    fn test_resize_block() {
        let mut hp = HashHeap::new();
        let p = hp.alloc(10);
        hp.set(p, 9, 45);
        hp.resize_block(p, 15, 33);
        assert_eq!(hp.heap[&p].len(), 15);
        assert_eq!(hp.get(p, 9), 45);
        assert_eq!(hp.get(p, 10), 33);
        assert_eq!(hp.get(p, 11), 33);
        assert_eq!(hp.get(p, 12), 33);
        assert_eq!(hp.get(p, 13), 33);
        assert_eq!(hp.get(p, 14), 33);
    }

    #[test]
    fn test_move_block_onto_heap() {
        let mut hp = HashHeap::new();
        let v = vec![-4, 8, 99];
        let p = hp.add_block(v);
        assert_eq!(hp.heap[&p], vec![-4, 8, 99]);
        assert_eq!(hp.idx, 1);
    }
}
