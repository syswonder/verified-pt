use crate::common::addr::PAddrExec;

/// An easy memory pool that uses a bitmap to track 4k physical frames.
#[repr(C, align(4096))]
pub struct FramePool {
    /// Memory region.
    pub mem: [u8; 0x100000],
    /// Bitmap of the physical frames.
    pub bitmap: [bool; 0x100],
}

impl FramePool {
    /// Create a new frame pool.
    pub fn new() -> Self {
        Self {
            bitmap: [false; 0x100],
            mem: [0; 0x100000],
        }
    }

    /// Allocate a 4k physical frame.
    pub fn alloc(&mut self) -> PAddrExec {
        let idx = self.bitmap.iter().position(|b| !b).unwrap();
        self.bitmap[idx] = true;
        PAddrExec(self.mem.as_ptr() as usize + idx as usize * 4096)
    }

    /// Deallocate a 4k physical frame.
    pub fn dealloc(&mut self, addr: PAddrExec) {
        let idx = (addr.0 - self.mem.as_ptr() as usize) / 4096;
        self.bitmap[idx] = false;
    }
}
