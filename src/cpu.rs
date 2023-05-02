use crate::opcode;
use bitflags::bitflags;

bitflags! {
    /// # Status Register (P) http://wiki.nesdev.com/w/index.php/Status_flags
    ///
    ///  7 6 5 4 3 2 1 0
    ///  N V _ B D I Z C
    ///  | |   | | | | +--- Carry Flag
    ///  | |   | | | +----- Zero Flag
    ///  | |   | | +------- Interrupt Disable
    ///  | |   | +--------- Decimal Mode (not used on NES)
    ///  | |   +----------- Break Command
    ///  | +--------------- Overflow Flag
    ///  +----------------- Negative Flag
    ///
    #[derive(Clone)]
    pub struct CpuFlags: u8 {
        const CARRY             = 0b00000001;
        const ZERO              = 0b00000010;
        const INTERRUPT_DISABLE = 0b00000100;
        const DECIMAL_MODE      = 0b00001000;
        const BREAK             = 0b00010000;
        const BREAK2            = 0b00100000;
        const OVERFLOW          = 0b01000000;
        const NEGATIVE          = 0b10000000;
    }
}

const STACK: u16 = 0x0100;
const STACK_RESET: u8 = 0xFD;

pub struct Cpu {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: CpuFlags,
    pub program_counter: u16,
    pub stack_pointer: u8,
    memory: [u8; 0xFFFF],
}

#[derive(Clone, Copy, Debug)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    IndirectX,
    IndirectY,
    NoneAddressing,
}

pub trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, addr: u16) -> u16 {
        u16::from_le_bytes([self.mem_read(addr), self.mem_read(addr + 1)])
    }

    fn mem_write_u16(&mut self, addr: u16, data: u16) {
        let [lo, hi] = data.to_le_bytes();
        self.mem_write(addr, lo);
        self.mem_write(addr + 1, hi);
    }
}

impl Mem for Cpu {
    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }
}

impl Cpu {
    pub fn new() -> Self {
        Self {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: CpuFlags::from_bits_truncate(0b100100),
            program_counter: 0,
            stack_pointer: STACK_RESET,
            memory: [0; 0xFFFF],
        }
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run(|_| {});
    }

    pub fn load(&mut self, program: Vec<u8>) {
        self.memory[0x0600..(0x0600 + program.len())].copy_from_slice(&program);
        self.mem_write_u16(0xFFFC, 0x0600);
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = CpuFlags::from_bits_truncate(0b100100);
        self.stack_pointer = STACK_RESET;

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn run<F>(&mut self, mut callback: F)
    where
        F: FnMut(&mut Self),
    {
        loop {
            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_save = self.program_counter;

            let opcode = opcode::CPU_OPCODE_MAP
                .get(&code)
                .unwrap_or_else(|| panic!("OpCode {:x} is not recognized", code));

            match code {
                // LDA
                0xA9 | 0xA5 | 0xB5 | 0xAD | 0xBD | 0xB9 | 0xA1 | 0xB1 => {
                    self.lda(opcode.mode);
                }
                // TAX
                0xAA => self.tax(),
                // INX
                0xE8 => self.inx(),
                // BRK
                0x00 => return,
                // CLD
                0xD8 => self.status.remove(CpuFlags::DECIMAL_MODE),
                // CLI
                0x58 => self.status.remove(CpuFlags::INTERRUPT_DISABLE),
                // CLV
                0xB8 => self.status.remove(CpuFlags::OVERFLOW),
                // CLC
                0x18 => self.status.remove(CpuFlags::CARRY),
                // SEC
                0x38 => self.status.insert(CpuFlags::CARRY),
                // SEI
                0x78 => self.status.insert(CpuFlags::INTERRUPT_DISABLE),
                // SED
                0xF8 => self.status.insert(CpuFlags::DECIMAL_MODE),
                // PHA
                0x48 => self.stack_push(self.register_a),
                // PLA
                0x68 => self.pla(),
                // PHP
                0x08 => self.php(),
                // PLP
                0x28 => self.plp(),
                // ADC
                0x69 | 0x65 | 0x75 | 0x6D | 0x7D | 0x79 | 0x61 | 0x71 => self.adc(opcode.mode),
                // SBC
                0xE9 | 0xE5 | 0xF5 | 0xED | 0xFD | 0xF9 | 0xE1 | 0xF1 => self.sbc(opcode.mode),
                // AND
                0x29 | 0x25 | 0x35 | 0x2D | 0x3D | 0x39 | 0x21 | 0x31 => self.and(opcode.mode),
                // EOR
                0x49 | 0x45 | 0x55 | 0x4D | 0x5D | 0x59 | 0x41 | 0x51 => self.eor(opcode.mode),
                // ORA
                0x09 | 0x05 | 0x15 | 0x0D | 0x1D | 0x19 | 0x01 | 0x11 => self.ora(opcode.mode),
                // LSR
                0x4a => self.lsr_accumulator(),
                // LSR
                0x46 | 0x56 | 0x4E | 0x5E => {
                    self.lsr(opcode.mode);
                }
                // ASL
                0x0A => self.asl_accumulator(),
                // ASL
                0x06 | 0x16 | 0x0E | 0x1E => {
                    self.asl(opcode.mode);
                }
                // ROL
                0x2A => self.rol_accumulator(),
                // ROL
                0x26 | 0x36 | 0x2E | 0x3E => {
                    self.rol(opcode.mode);
                }
                // ROR
                0x6A => self.ror_accumulator(),
                /* ROR */
                0x66 | 0x76 | 0x6E | 0x7E => {
                    self.ror(opcode.mode);
                }
                // INC
                0xE6 | 0xF6 | 0xEE | 0xFE => {
                    self.inc(opcode.mode);
                }
                // INY
                0xC8 => self.iny(),
                // DEC
                0xC6 | 0xD6 | 0xCE | 0xDE => {
                    self.dec(opcode.mode);
                }
                // DEX
                0xCA => self.dex(),
                // DEY
                0x88 => self.dey(),
                // CMP
                0xC9 | 0xC5 | 0xD5 | 0xCD | 0xDD | 0xD9 | 0xC1 | 0xD1 => {
                    self.compare(opcode.mode, self.register_a)
                }
                // CPY
                0xC0 | 0xC4 | 0xCC => self.compare(opcode.mode, self.register_y),
                // CPX
                0xE0 | 0xE4 | 0xEC => self.compare(opcode.mode, self.register_x),
                // JMP Absolute
                0x4C => {
                    let mem_address = self.mem_read_u16(self.program_counter);
                    self.program_counter = mem_address;
                }
                // JMP Indirect
                0x6C => {
                    let mem_address = self.mem_read_u16(self.program_counter);
                    // let indirect_ref = self.mem_read_u16(mem_address);
                    // 6502 bug mode with with page boundary:
                    //   if address $3000 contains $40, $30FF contains $80, and $3100 contains $50,
                    //   the result of JMP ($30FF) will be a transfer of control to $4080 rather than $5080 as you intended
                    // i.e. the 6502 took the low byte of the address from $30FF and the high byte from $3000

                    let indirect_ref = if mem_address & 0x00FF == 0x00FF {
                        let lo = self.mem_read(mem_address);
                        let hi = self.mem_read(mem_address & 0xFF00);
                        u16::from_le_bytes([lo, hi])
                    } else {
                        self.mem_read_u16(mem_address)
                    };

                    self.program_counter = indirect_ref;
                }
                // JSR
                0x20 => {
                    self.stack_push_u16(self.program_counter + 2 - 1);
                    let target_address = self.mem_read_u16(self.program_counter);
                    self.program_counter = target_address;
                }
                // RTS
                0x60 => self.program_counter = self.stack_pop_u16() + 1,
                // RTI
                0x40 => {
                    self.status = CpuFlags::from_bits(self.stack_pop()).unwrap();
                    self.status.remove(CpuFlags::BREAK);
                    self.status.insert(CpuFlags::BREAK2);

                    self.program_counter = self.stack_pop_u16();
                }
                // BNE
                0xD0 => self.branch(!self.status.contains(CpuFlags::ZERO)),
                // BVS
                0x70 => self.branch(self.status.contains(CpuFlags::OVERFLOW)),
                // BVC
                0x50 => self.branch(!self.status.contains(CpuFlags::OVERFLOW)),
                // BPL
                0x10 => self.branch(!self.status.contains(CpuFlags::NEGATIVE)),
                // BMI
                0x30 => self.branch(self.status.contains(CpuFlags::NEGATIVE)),
                // BEQ
                0xF0 => self.branch(self.status.contains(CpuFlags::ZERO)),
                // BCS
                0xB0 => self.branch(self.status.contains(CpuFlags::CARRY)),
                // BCC
                0x90 => self.branch(!self.status.contains(CpuFlags::CARRY)),
                // BIT
                0x24 | 0x2C => self.bit(opcode.mode),
                // STA
                0x85 | 0x95 | 0x8D | 0x9D | 0x99 | 0x81 | 0x91 => self.sta(opcode.mode),
                // STX
                0x86 | 0x96 | 0x8E => {
                    let addr = self.get_operand_address(opcode.mode);
                    self.mem_write(addr, self.register_x);
                }
                // STY
                0x84 | 0x94 | 0x8C => {
                    let addr = self.get_operand_address(opcode.mode);
                    self.mem_write(addr, self.register_y);
                }
                // LDX
                0xA2 | 0xA6 | 0xB6 | 0xAE | 0xBE => self.ldx(opcode.mode),
                // LDY
                0xA0 | 0xA4 | 0xB4 | 0xAC | 0xBC => self.ldy(opcode.mode),
                // NOP
                0xEA => {} // do nothing
                // TAY
                0xA8 => {
                    self.register_y = self.register_a;
                    self.update_zero_and_negative_flags(self.register_y);
                }
                // TSX
                0xBA => {
                    self.register_x = self.stack_pointer;
                    self.update_zero_and_negative_flags(self.register_x);
                }
                // TXA
                0x8A => {
                    self.register_a = self.register_x;
                    self.update_zero_and_negative_flags(self.register_a);
                }
                // TXS
                0x9A => self.stack_pointer = self.register_x,
                // TYA
                0x98 => {
                    self.register_a = self.register_y;
                    self.update_zero_and_negative_flags(self.register_a);
                }

                _ => panic!("OpCode {:x} is not implemented", code),
            }

            if program_counter_save == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }

            callback(self);
        }
    }

    // 6502 CPU instructions

    fn adc(&mut self, mode: AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.add_to_register_a(data);
    }

    fn and(&mut self, mode: AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.set_register_a(data & self.register_a);
    }

    fn asl(&mut self, mode: AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        self.status.set(CpuFlags::CARRY, data >> 7 == 1);
        data <<= 1;
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn bit(&mut self, mode: AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        let and = self.register_a & data;
        self.status.set(CpuFlags::ZERO, and == 0);
        self.status.set(CpuFlags::NEGATIVE, data & 0b1000_0000 > 0);
        self.status.set(CpuFlags::OVERFLOW, data & 0b0100_0000 > 0);
    }

    fn dec(&mut self, mode: AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        data = data.wrapping_sub(1);
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn eor(&mut self, mode: AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.set_register_a(data ^ self.register_a);
    }

    fn inc(&mut self, mode: AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        data = data.wrapping_add(1);
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn lda(&mut self, mode: AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.set_register_a(data);
    }

    fn ldx(&mut self, mode: AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.register_x = data;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn ldy(&mut self, mode: AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.register_y = data;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn lsr(&mut self, mode: AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        self.status.set(CpuFlags::CARRY, data & 1 == 1);
        data >>= 1;
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn ora(&mut self, mode: AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.set_register_a(data | self.register_a);
    }

    fn php(&mut self) {
        //http://wiki.nesdev.com/w/index.php/CPU_status_flag_behavior
        let mut flags = self.status.clone();
        flags.insert(CpuFlags::BREAK);
        flags.insert(CpuFlags::BREAK2);
        self.stack_push(flags.bits());
    }

    fn pla(&mut self) {
        let data = self.stack_pop();
        self.set_register_a(data);
    }

    fn plp(&mut self) {
        self.status = CpuFlags::from_bits(self.stack_pop()).unwrap();
        self.status.remove(CpuFlags::BREAK);
        self.status.insert(CpuFlags::BREAK2);
    }

    fn rol(&mut self, mode: AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        let carry_save = self.status.contains(CpuFlags::CARRY);
        self.status.set(CpuFlags::CARRY, data >> 7 == 1);
        data <<= 1;
        if carry_save {
            data |= 1;
        }
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn ror(&mut self, mode: AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        let carry_save = self.status.contains(CpuFlags::CARRY);
        self.status.set(CpuFlags::CARRY, data & 1 == 1);
        data >>= 1;
        if carry_save {
            data |= 0b1000_0000;
        }
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn sbc(&mut self, mode: AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.add_to_register_a((data as i8).wrapping_neg().wrapping_sub(1) as u8);
    }

    fn sta(&mut self, mode: AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    // Utility methods

    /// note: ignoring decimal mode
    /// http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
    fn add_to_register_a(&mut self, data: u8) {
        let sum =
            self.register_a as u16 + data as u16 + self.status.contains(CpuFlags::CARRY) as u16;
        self.status.set(CpuFlags::CARRY, sum > 0xFF);

        let result = sum as u8;

        let overflow = (data ^ result) & (result ^ self.register_a) & 0x80 != 0;
        self.status.set(CpuFlags::OVERFLOW, overflow);

        self.set_register_a(result);
    }

    fn asl_accumulator(&mut self) {
        let mut data = self.register_a;
        self.status.set(CpuFlags::CARRY, data >> 7 == 1);
        data <<= 1;
        self.set_register_a(data);
    }

    fn branch(&mut self, condition: bool) {
        if condition {
            let jump = self.mem_read(self.program_counter) as i8;
            let jump_addr = self
                .program_counter
                .wrapping_add(1)
                .wrapping_add(jump as u16);

            self.program_counter = jump_addr;
        }
    }

    fn compare(&mut self, mode: AddressingMode, compare_with: u8) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.status.set(CpuFlags::CARRY, data <= compare_with);
        self.update_zero_and_negative_flags(compare_with.wrapping_sub(data));
    }

    fn get_operand_address(&self, mode: AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::ZeroPageX => self
                .mem_read(self.program_counter)
                .wrapping_add(self.register_x) as u16,
            AddressingMode::ZeroPageY => self
                .mem_read(self.program_counter)
                .wrapping_add(self.register_y) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::AbsoluteX => self
                .mem_read_u16(self.program_counter)
                .wrapping_add(self.register_x as u16),
            AddressingMode::AbsoluteY => self
                .mem_read_u16(self.program_counter)
                .wrapping_add(self.register_y as u16),
            AddressingMode::IndirectX => {
                let base = self.mem_read(self.program_counter);

                let ptr = base.wrapping_add(self.register_x) as u16;
                let lo = self.mem_read(ptr);
                let hi = self.mem_read(ptr.wrapping_add(1));
                u16::from_le_bytes([lo, hi])
            }
            AddressingMode::IndirectY => {
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read(base.wrapping_add(1) as u16);
                u16::from_le_bytes([lo, hi]).wrapping_add(self.register_y as u16)
            }
            _ => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn lsr_accumulator(&mut self) {
        let mut data = self.register_a;
        self.status.set(CpuFlags::CARRY, data & 1 == 1);
        data >>= 1;
        self.set_register_a(data)
    }

    fn rol_accumulator(&mut self) {
        let mut data = self.register_a;
        let carry_save = self.status.contains(CpuFlags::CARRY);
        self.status.set(CpuFlags::CARRY, data >> 7 == 1);
        data <<= 1;
        if carry_save {
            data |= 1;
        }
        self.set_register_a(data);
    }

    fn ror_accumulator(&mut self) {
        let mut data = self.register_a;
        let carry_save = self.status.contains(CpuFlags::CARRY);
        self.status.set(CpuFlags::CARRY, data & 1 == 1);
        data >>= 1;
        if carry_save {
            data |= 0b1000_0000;
        }
        self.set_register_a(data);
    }

    fn set_register_a(&mut self, data: u8) {
        self.register_a = data;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn stack_pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read(STACK + self.stack_pointer as u16)
    }

    fn stack_pop_u16(&mut self) -> u16 {
        let lo = self.stack_pop();
        let hi = self.stack_pop();
        u16::from_le_bytes([lo, hi])
    }

    fn stack_push(&mut self, data: u8) {
        self.mem_write(STACK + self.stack_pointer as u16, data);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    fn stack_push_u16(&mut self, data: u16) {
        let [lo, hi] = data.to_le_bytes();
        self.stack_push(hi);
        self.stack_push(lo);
    }

    fn update_zero_and_negative_flags(&mut self, data: u8) {
        self.status.set(CpuFlags::ZERO, data == 0);
        self.status.set(CpuFlags::NEGATIVE, data & 0b1000_0000 != 0);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_0xa9_lda_immediate_load_data() {
        let mut cpu = Cpu::new();
        cpu.load_and_run(vec![0xA9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        assert!(!cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
    }

    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let mut cpu = Cpu::new();
        cpu.load_and_run(vec![0xA9, 0x0A, 0xAA, 0x00]);
        assert_eq!(cpu.register_x, 10)
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = Cpu::new();
        cpu.load_and_run(vec![0xA9, 0xC0, 0xAA, 0xE8, 0x00]);
        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = Cpu::new();
        cpu.load_and_run(vec![0xA9, 0xFF, 0xAA, 0xE8, 0xE8, 0x00]);
        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_lda_from_memory() {
        let mut cpu = Cpu::new();
        cpu.mem_write(0x10, 0x55);
        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);
        assert_eq!(cpu.register_a, 0x55);
    }
}
