#[derive(Clone, Copy, Debug, PartialEq)]
enum ByteLv<'t> {
    Reg(Register),
    R,
    I,
    BptrHL,
    Bdsp(IndexRegister, i8),
    BptrBC,
    BptrDE,
    Bptr(WordExpr<'t>),
}

impl<'t> ByteLv<'t> {
    fn mnemonic(self) -> String {
        use ByteLv::*;
        match self {
            Reg(r) => r.mnemonic().to_owned(),
            R => "R".to_owned(),
            I => "I".to_owned(),
            BptrHL => "(HL)".to_owned(),
            Bdsp(i, d) => format!("({}+{})", i.mnemonic(), d),
            BptrBC => "(BC)".to_owned(),
            BptrDE => "(DE)".to_owned(),
            Bptr(nn) => nn.mnemonic(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum ByteRv<'t> {
    Bexp(ByteExpr<'t>),
    Blv(ByteLv<'t>),
}

impl<'t> ByteRv<'t> {
    fn mnemonic(self) -> String {
        match self {
            ByteRv::Bexp(n) => n.mnemonic(),
            ByteRv::Blv(lv) => lv.mnemonic(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum WordLv<'t> {
    Pair1(RegisterPair1),
    Pair2(RegisterPair2),
    Ind(IndexRegister),
    Wptr(WordExpr<'t>),
}

impl<'t> WordLv<'t> {
    fn try_ss(self) -> Option<RegisterPair2> {
        use WordLv::*;
        match self {
            Pair1(RegisterPair1::BC) => Some(RegisterPair2::BC),
            Pair1(RegisterPair1::DE) => Some(RegisterPair2::DE),
            Pair1(RegisterPair1::HL) => Some(RegisterPair2::HL),
            Pair2(ss) => Some(ss),
            _ => None,
        }
    }
    fn try_dd(self) -> Option<RegisterPair2> {
        self.try_ss()
    }
    fn mnemonic(self) -> String {
        use WordLv::*;
        match self {
            Pair1(qq) => qq.mnemonic().to_owned(),
            Pair2(dd) => dd.mnemonic().to_owned(),
            Ind(i) => i.mnemonic().to_owned(),
            Wptr(nn) => format!("({})", nn.mnemonic()),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum WordRv<'t> {
    Wexp(WordExpr<'t>),
    Wlv(WordLv<'t>),
}

impl<'t> WordRv<'t> {
    fn mnemonic(self) -> String {
        match self {
            WordRv::Wexp(nn) => nn.mnemonic(),
            WordRv::Wlv(lv) => lv.mnemonic(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Reg16 {
    AF, BC, DE, HL, IX, IY, SP,
}

impl Reg16 {
    fn to_qq(self) -> Option<RegisterPair1> {
        use Reg16::*;
        match self {
            AF => Some(RegisterPair1::AF),
            BC => Some(RegisterPair1::BC),
            DE => Some(RegisterPair1::DE),
            HL => Some(RegisterPair1::HL),
            _ => None,
        }
    }
    fn to_i(self) -> Option<IndexRegister> {
        use Reg16::*;
        match self {
            IX => Some(IndexRegister::IX),
            IY => Some(IndexRegister::IY),
            _ => None,
        }
    }
    fn mnemonic(self) -> &'static str {
        use Reg16::*;
        match self {
            AF => "AF",
            BC => "BC",
            DE => "DE",
            HL => "HL",
            IX => "IX",
            IY => "IY",
            SP => "SP",
        }
    }
}

// `qq`
#[derive(Clone, Copy, Debug, PartialEq)]
enum RegisterPair1 {
    BC, DE, HL, AF
}

impl RegisterPair1 {
    fn qq(self) -> u8 {
        use RegisterPair1::*;
        match self {
            BC => 0b00,
            DE => 0b01,
            HL => 0b10,
            AF => 0b11,
        }
    }
    fn mnemonic(self) -> &'static str {
        use RegisterPair1::*;
        match self {
            BC => "BC",
            DE => "DE",
            HL => "HL",
            AF => "AF",
        }
    }
}

// `dd`, `ss`
#[derive(Clone, Copy, Debug, PartialEq)]
enum RegisterPair2 {
    BC, DE, HL, SP
}

impl RegisterPair2 {
    fn dd(self) -> u8 {
        use RegisterPair2::*;
        match self {
            BC => 0b00,
            DE => 0b01,
            HL => 0b10,
            SP => 0b11,
        }
    }
    fn ss(self) -> u8 {
        self.dd()
    }
    fn mnemonic(self) -> &'static str {
        use RegisterPair2::*;
        match self {
            BC => "BC",
            DE => "DE",
            HL => "HL",
            SP => "SP",
        }
    }
}

// `pp`
#[derive(Clone, Copy, Debug)]
enum RegisterPairX {
    BC, DE, IX, SP
}

impl RegisterPairX {
    fn pp(self) -> u8 {
        use RegisterPairX::*;
        match self {
            BC => 0b00,
            DE => 0b01,
            IX => 0b10,
            SP => 0b11,
        }
    }
    fn mnemonic(self) -> &'static str {
        use RegisterPairX::*;
        match self {
            BC => "BC",
            DE => "DE",
            IX => "IX",
            SP => "SP",
        }
    }
}
// `rr`
#[derive(Clone, Copy, Debug)]
enum RegisterPairY {
    BC, DE, IY, SP
}

impl RegisterPairY {
    fn rr(self) -> u8 {
        use RegisterPairY::*;
        match self {
            BC => 0b00,
            DE => 0b01,
            IY => 0b10,
            SP => 0b11,
        }
    }
    fn mnemonic(self) -> &'static str {
        use RegisterPairY::*;
        match self {
            BC => "BC",
            DE => "DE",
            IY => "IY",
            SP => "SP",
        }
    }
}

// `r`
#[derive(Clone, Copy, Debug, PartialEq)]
enum Register {
    A, B, C, D, E, H, L
}

impl Register {
    fn r(self) -> u8 {
        use Register::*;
        match self {
            A => 0b111,
            B => 0b000,
            C => 0b001,
            D => 0b010,
            E => 0b011,
            H => 0b100,
            L => 0b101,
        }
    }
    fn mnemonic(self) -> &'static str {
        use Register::*;
        match self {
            A => "A",
            B => "B",
            C => "C",
            D => "D",
            E => "E",
            H => "H",
            L => "L",
        }
    }
}

// `i` (custom)
#[derive(Clone, Copy, Debug, PartialEq)]
enum IndexRegister {
    IX, IY
}

impl IndexRegister {
    fn i(self) -> u8 {
        use IndexRegister::*;
        match self {
            IX => 0xDD,
            IY => 0xFD,
        }
    }
    fn mnemonic(self) -> &'static str {
        use IndexRegister::*;
        match self {
            IX => "IX",
            IY => "IY",
        }
    }
}


// `ii` (custom)
#[derive(Clone, Copy, Debug)]
enum IndexRegisterEx {
    HL, IX, IY
}

impl IndexRegisterEx {
    fn prefix_length(self, l: usize) -> usize {
        use IndexRegisterEx::*;
        match self {
            HL => l,
            IX | IY => 1 + l,
        }
    }
    fn prefix_code(self, c: Code) -> Code {
        use IndexRegisterEx::*;
        match self {
            HL => c,
            IX => c.add_prefix(0xDD),
            IY => c.add_prefix(0xFD),
        }
    }
    fn mnemonic(self) -> &'static str {
        use IndexRegisterEx::*;
        match self {
            HL => "HL",
            IX => "IX",
            IY => "IY",
        }
    }
    fn prefix_tstates(self, ts: &'static [usize]) -> TStates {
        use IndexRegisterEx::*;
        use TStates::*;
        match self {
            HL => Always(ts),
            IX | IY => PrefixedAlways(4, ts),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Program {
    P00, P08, P10, P18, P20, P28, P30, P38
}

impl Program {
    fn p(self) -> u8 {
        use Program::*;
        match self {
            P00 => 0b000,
            P08 => 0b001,
            P10 => 0b010,
            P18 => 0b011,
            P20 => 0b100,
            P28 => 0b101,
            P30 => 0b110,
            P38 => 0b111,
        }
    }
    fn mnemonic(self) -> &'static str {
        use Program::*;
        match self {
            P00 => "#00",
            P08 => "#08",
            P10 => "#10",
            P18 => "#18",
            P20 => "#20",
            P28 => "#28",
            P30 => "#30",
            P38 => "#38",
        }
    }
}

#[derive (Debug)]
enum TStates {
    Never, // for data
    Always(&'static [usize]),
    PrefixedAlways(usize, &'static [usize]),
    Either(&'static [usize], &'static [usize]),
}

struct Code {
    seq: [u8; 4],
    len: usize,
}

impl Code {
    fn add_prefix(self, p: u8) -> Code {
        match self.len {
            1 => Code { len: 2, seq: [p, self.seq[0], 0,           0          ] },
            2 => Code { len: 3, seq: [p, self.seq[0], self.seq[1], 0          ] },
            3 => Code { len: 4, seq: [p, self.seq[0], self.seq[1], self.seq[2]] },
            _ => panic!("bad code seq length"),
        }
    }
    fn bytes(&self) -> &[u8] {
        &self.seq[0..self.len]
    }
}

impl From<u8> for Code {
    fn from(b: u8) -> Code {
        Code {
            seq: [b, 0, 0, 0],
            len: 1,
        }
    }
}
impl From<(u8, u8)> for Code {
    fn from(p: (u8, u8)) -> Code {
        Code {
            seq: [p.0, p.1, 0, 0],
            len: 2,
        }
    }
}
impl From<(u8, u8, u8)> for Code {
    fn from(p: (u8, u8, u8)) -> Code {
        Code {
            seq: [p.0, p.1, p.2, 0],
            len: 3,
        }
    }
}
impl From<(u8, u8, u8, u8)> for Code {
    fn from(p: (u8, u8, u8, u8)) -> Code {
        Code {
            seq: [p.0, p.1, p.2, p.3],
            len: 4,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum ByteExpr<'t> {
    Immediate(u8),
    Const(&'t str),
    LabelHi(&'t str),
    LabelLo(&'t str),
}

impl<'t> ByteExpr<'t> {
    fn mnemonic(self) -> String {
        use ByteExpr::*;
        match self {
            Immediate(b) => format!("{}", b),
            Const(c) => format!("${}", c),
            LabelHi(l) => format!("!hi(@{})", l),
            LabelLo(l) => format!("!lo(@{})", l),
        }
    }
    fn eval(
        self, ctx: &dyn Lookup
    ) -> Result<u8, EncodeError> {
        use ByteExpr::*;
        match self {
            Immediate(b) => Ok(b),
            Const(c) => ctx.get_byte_const(c).ok_or(EncodeError::UnknownByteConst),
            LabelHi(l) =>
                ctx.label2addr(l).map(|addr| ((addr >> 8) & 0xFF) as u8),
            LabelLo(l) =>
                ctx.label2addr(l).map(|addr| (addr & 0xFF) as u8),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum WordExpr<'t> {
    Immediate(u16),
    Const(&'t str),
    HiLo(ByteExpr<'t>, ByteExpr<'t>),
    Label(&'t str),
}

impl<'t> WordExpr<'t> {
    fn mnemonic(self) -> String {
        use WordExpr::*;
        match self {
            Immediate(w) => format!("{}", w),
            Const(c) => format!("$${}", c),
            HiLo(h, l) => format!("{}:{}", h.mnemonic(), l.mnemonic()),
            Label(l) => format!("@{}", l),
        }
    }
    fn eval(self, ctx: &dyn Lookup) -> Result<u16, EncodeError> {
        use WordExpr::*;
        match self {
            Immediate(w) => Ok(w),
            Const(c) => ctx.get_word_const(c).ok_or(EncodeError::UnknownWordConst),
            HiLo(h, l) => h.eval(ctx).and_then(|h| l.eval(ctx).map(|l| ((h as u16) * 256 + l as u16))),
            Label(l) => ctx.label2addr(l).map(|x| x as u16),
        }
    }
    fn encode(self, ctx: &dyn Lookup) -> Result<(u8, u8), EncodeError> {
        self.eval(ctx).map(|w| { let lh = w.to_le_bytes(); (lh[0], lh[1]) })
    }
}

// `cc`
#[derive(Clone, Copy, Debug, PartialEq)]
enum Condition {
    NZ, Z, NC, C, PO, PE, P, M
}

impl Condition {
    fn cc(self) -> u8 {
        use Condition::*;
        match self {
            NZ => 0b000,
            Z =>  0b001,
            NC => 0b010,
            C =>  0b011,
            PO => 0b100,
            PE => 0b101,
            P =>  0b110,
            M =>  0b111,
        }
    }
    fn mnemonic(self) -> &'static str {
        use Condition::*;
        match self {
            NZ => "NZ",
            Z =>  "Z",
            NC => "NC",
            C =>  "C",
            PO => "PO",
            PE => "PE",
            P =>  "P",
            M =>  "M",
        }
    }
}

// `s`
#[derive(Clone, Copy, Debug)]
enum ArithmeticOperand<'t> {
    Xr(Register),
    Xn(ByteExpr<'t>),
    PHL,
    Pid(IndexRegister, i8),
}

impl<'t> ArithmeticOperand<'t> {
    fn tstates(self) -> TStates {
        use ArithmeticOperand::*;
        use TStates::*;
        match self {
            Xr(_) => Always(&[4]),
            Xn(_) => Always(&[4, 3]),
            PHL => Always(&[4, 3]),
            Pid(_, _) => Always(&[4, 4, 3, 5, 3]),
        }
    }
    fn mnemonic(self) -> String {
        use ArithmeticOperand::*;
        match self {
            Xr(r) => r.mnemonic().to_owned(),
            Xn(n) => n.mnemonic(),
            PHL => "(HL)".to_owned(),
            Pid(i, d) => if d < 0 {
                format!("({}{})", i.mnemonic(), d)
            } else {
                format!("({}+{})", i.mnemonic(), d)
            },
        }
    }
}

// `m`
#[derive(Clone, Copy, Debug)]
enum IncDecOperand {
    Xr(Register),
    PHL,
    Pid(IndexRegister, i8),
}

impl IncDecOperand {
    fn tstates(self) -> TStates {
        use IncDecOperand::*;
        use TStates::*;
        match self {
            Xr(_) => Always(&[4]),
            PHL => Always(&[4, 4, 3]),
            Pid(_, _) => Always(&[4, 4, 3, 5, 4, 3]),
        }
    }
    fn mnemonic(self) -> String {
        use IncDecOperand::*;
        match self {
            Xr(r) => r.mnemonic().to_owned(),
            PHL => "(HL)".to_owned(),
            Pid(i, d) => if d < 0 {
                format!("({}{})", i.mnemonic(), d)
            } else {
                format!("({}+{})", i.mnemonic(), d)
            },
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Instruction<'t> {
    // Pseudo
    DbXn(ByteExpr<'t>),
    DwXnn(WordExpr<'t>),

    Ld8(ByteLv<'t>, ByteRv<'t>),

/*
    // 8-Bit Load Group
    LdXrXr(Register, Register),                 // LD r, r'
    LdXrXn(Register, ByteExpr<'t>),             // LD r, n
    LdXrPHL(Register),                         // LD r, (HL)
    LdXrPid(Register, IndexRegister, i8),      // LD r, (IX/IY+d)
    LdPHLXr(Register),                         // LD (HL), r
    LdPidXr(IndexRegister, i8, Register),      // LD (IX/IY+d), r
    LdPHLXn(ByteExpr<'t>),                     // LD (HL), n
    LdPidXn(IndexRegister, i8, ByteExpr<'t>),  // LD (IX/IY+d), n
    LdAPBC,                                   // LD A, (BC)
    LdAPDE,                                   // LD A, (DE)
    LdAPnn(WordExpr<'t>),                     // LD A, (nn)
    LdPBCA,                                   // LD (BC), A
    LdPDEA,                                   // LD (DE), A
    LdPnnA(WordExpr<'t>),                     // LD (nn), A
    LdAI,                                     // LD A, I
    LdAR,                                     // LD A, R
    LdIA,                                     // LD I, A
    LdRA,                                     // LD R, A
*/
/*    
    // 16-Bit Load Group
    LdXddXnn(RegisterPair2, WordExpr<'t>),    // LD dd, nn
    LdXiiXnn(IndexRegisterEx, WordExpr<'t>),  // LD HL/IX/IY, nn // LdXiiXnn(HL, ..) == LdXddXnn(HL, ..)
    LdXddPnn(RegisterPair2, WordExpr<'t>),    // LD dd, (nn)     // ambiguous LD HL, (nn)
    LdXiiPnn(IndexRegisterEx, WordExpr<'t>),  // LD HL/IX/IY, (nn)
    LdPnnXdd(WordExpr<'t>, RegisterPair2),    // LD (nn), dd     // ambiguous LD (nn), HL
    LdPnnXii(WordExpr<'t>, IndexRegisterEx),  // LD (nn), HL/IX/IY
    LdSPXii(IndexRegisterEx),                 // LD SP, HL/IX/IY
    PushXqq(RegisterPair1),                   // PUSH dd         // PushXdd(HL) === PushXii(HL)
    PushXii(IndexRegisterEx),                 // PUSH HL/IX/IY
    PopXqq(RegisterPair1),                    // POP dd          // same ^^
    PopXii(IndexRegisterEx),                  // POP HL/IX/IY
*/
    Ld16(WordLv<'t>, WordRv<'t>),
    Push(WordRv<'t>),
    Pop(WordLv<'t>),

/*
    // Exchange, Block Transfer, and Search Group
    ExDEHL,
    ExAFAF,
    Exx,
    ExPSPXii(IndexRegisterEx),
    Ldi, Ldir, Ldd, Lddr,
    Cpi, Cpir, Cpd, Cpdr,

    // 8-Bit Arithmetic Group
    AddAXs(ArithmeticOperand<'t>),
    AdcAXs(ArithmeticOperand<'t>),
    SubXs(ArithmeticOperand<'t>),
    SbcAXs(ArithmeticOperand<'t>),
    AndXs(ArithmeticOperand<'t>),
    OrXs(ArithmeticOperand<'t>),
    XorXs(ArithmeticOperand<'t>),
    CpXs(ArithmeticOperand<'t>),
    IncXm(IncDecOperand),
    DecXm(IncDecOperand),
*/
    // General-Purpose Arithmetic and CPU Control Group
    Daa, Cpl, Neg, Ccf, Scf,
    Nop,
    Halt,
    Di, Ei,
    Im0, Im1, Im2,
/*
    // 16-Bit Arithmetic Group
    AddHLXss(RegisterPair2),
    AdcHLXss(RegisterPair2),
    SbcHLXss(RegisterPair2),
    AddIXXpp(RegisterPairX),
    AddIYXrr(RegisterPairY),
    IncXss(RegisterPair2),
    IncXi(IndexRegister),
    DecXss(RegisterPair2),
    DecXi(IndexRegister),
*/

    Inc16(WordLv<'t>),
    Dec16(WordLv<'t>),
/*
    // Jump Group
    JpXnn(JumpTarget<'t>),
    JpXccXnn(Condition, JumpTarget<'t>),
    JrXe(JumpTarget<'t>),
    JrCXe(JumpTarget<'t>),
    JrNcXe(JumpTarget<'t>),
    JrZXe(JumpTarget<'t>),
    JrNzXe(JumpTarget<'t>),
    JpPii(IndexRegisterEx), // JP (HL/IX/IY)
    DjnzXe(JumpTarget<'t>),
    // Call and Return Group
    CallXnn(JumpTarget<'t>),
    CallXccXnn(Condition, JumpTarget<'t>),
*/

    Jp(JumpTarget<'t>),
    JpIf(Condition, JumpTarget<'t>),
    Jr(JumpTarget<'t>),
    JrIf(Condition, JumpTarget<'t>),
    Djnz(JumpTarget<'t>),

    Call(JumpTarget<'t>),
    CallIf(Condition, JumpTarget<'t>),
    Ret,
    RetIf(Condition),
    Reti,
    Retn,
    Rst(Program),
/*
    // Input and Output Group
    OutPnA(ByteExpr<'t>), // OUT (n), A
    OutPCXr(Register), // OUT (C), r
*/
    Out(ByteRv<'t>, ByteRv<'t>),
}

#[derive(Debug)]
enum EncodeError {
    UnknownLabel,
    UnknownByteConst,
    UnknownWordConst,
    RelativeJumpTooFar,
    JumpOutOfCode,
    InvalidInstruction,
}

use std::collections::HashMap;

fn addr2rel(addr: usize, cur: usize) -> Result<i8, EncodeError> {
    // i8 -128..127
    if addr < cur && cur - addr <= 128 {
        let d = (cur-addr) as isize;
        Ok((-d) as i8)
    } else if addr >= cur && addr - cur < 128 {
        Ok((addr-cur) as i8)
    } else {
        println!("addr={}, cur={}", addr, cur);
        Err(EncodeError::RelativeJumpTooFar)
    }
}

trait Lookup {
    fn label2addr(&self, label: &str) -> Result<usize, EncodeError>;
    fn get_byte_const(&self, name: &str) -> Option<u8>;
    fn get_word_const(&self, name: &str) -> Option<u16>;
}

struct TrueLookup<'t> {
    byte_consts: HashMap<&'t str, u8>,
    word_consts: HashMap<&'t str, u16>,
    labels: HashMap<&'t str, usize>
}

impl<'t> TrueLookup<'t> {
    fn new() -> Self {
        Self {
            byte_consts: HashMap::default(),
            word_consts: HashMap::default(),
            labels: HashMap::default(),
        }
    }
}

impl<'t> Lookup for TrueLookup<'t> {
    fn label2addr(&self, label: &str) -> Result<usize, EncodeError> {
        self.labels.get(label).copied().ok_or(EncodeError::UnknownLabel)
    }
    fn get_byte_const(&self, name: &str) -> Option<u8> {
        self.byte_consts.get(name).copied()
    }
    fn get_word_const(&self, name: &str) -> Option<u16> {
        self.word_consts.get(name).copied()
    }
}

struct FakeLookup {}

impl Lookup for FakeLookup {
    fn label2addr(&self, _: &str) -> Result<usize, EncodeError> {
        Ok(0)
    }
    fn get_byte_const(&self, _: &str) -> Option<u8> {
        Some(0)
    }
    fn get_word_const(&self, _: &str) -> Option<u16> {
        Some(0)
    }
}

fn encode(i: i8) -> u8 {
    i.to_le_bytes()[0]
}

impl<'a> Instruction<'a> {
    fn length(self) -> Result<usize, EncodeError> {
        self.encode(0, &FakeLookup {}).map(|c| c.len)
/*          
        use Instruction::*;
        match self {
            DbXn(_) => 1,
            DwXnn(_) => 2,
            LdXrXn(_, _) => 2,
            LdIA => 2,
            PushXqq(_) | PopXqq(_) => 1,
            PushXii(ii) => ii.prefix_length(1),
            PopXii(ii) => ii.prefix_length(1),
            Nop | Halt | Di | Ei => 1,
            Im0 | Im1 | Im2 => 2,
            JrXe(_) => 2,
            JrNzXe(_) => 2,
            DjnzXe(_) => 2,
            CallXnn(_) => 3,
            Ret => 1,
            Reti => 2,
            OutPnA(_) => 2,
            OutPCXr(_) => 2,
        }
*/
    }
    fn encode(self, addr: usize, ctx: &dyn Lookup) -> Result<Code, EncodeError>  {
        use Instruction::*;
        use ByteLv::*;
        use ByteRv::*;
        use WordLv::*;
        use WordRv::*;
        use Register::*;
        use RegisterPair2::HL;
        use RegisterPair2::SP;
        const B_01_RRR_RRR: u8 = 0b01_000_000;
        const B_00_RRR_110: u8 = 0b00_000_110;
        const B_01_RRR_110: u8 = 0b01_000_110;
        const B_01_110_RRR: u8 = 0b01_110_000;
        const B_01_DD_0011: u8 = 0b01_00_0011;
        const B_01_DD_1011: u8 = 0b01_00_1011;
        const B_11_CCC_100: u8 = 0b11_000_100;
        const B_11_CCC_000: u8 = 0b11_000_000;
        const B_11_TTT_111: u8 = 0b11_000_111;
        const B_01_RRR_001: u8 = 0b01_000_001;
        const B_11_CCC_010: u8 = 0b11_000_010;
        const B_00_SS_0011: u8 = 0b00_00_0011;
        const B_00_SS_1011: u8 = 0b00_00_1011;
        match self {
            DbXn(n) => n.eval(ctx).map(|n| n.into()),
            DwXnn(nn) => nn.encode(ctx).map(|(l, h)| (l, h).into()),

            Ld8(Reg(r), Blv(Reg(t))) => Ok(                          (       B_01_RRR_RRR | (r.r() << 3) | t.r()    ).into()),
            Ld8(Reg(r), Bexp(n)) => n.eval(ctx).map(|n|              (       B_00_RRR_110 | (r.r() << 3), n         ).into()),
            Ld8(Reg(r), Blv(BptrHL)) => Ok(                          (       B_01_RRR_110 | (r.r() << 3)            ).into()),
            Ld8(Reg(r), Blv(Bdsp(i, d))) => Ok(                      (i.i(), B_01_RRR_110 | (r.r() << 3), encode(d) ).into()),
            Ld8(BptrHL, Blv(Reg(r))) => Ok(                          (       B_01_110_RRR | r.r()                   ).into()),
            Ld8(Bdsp(i, d), Blv(Reg(r))) => Ok(                      (i.i(), B_01_110_RRR | r.r(),        encode(d) ).into()),
            Ld8(BptrHL, Bexp(n)) => n.eval(ctx).map(|n|              (       0b00_110_110, n                        ).into()),
            Ld8(Bdsp(i, d), Bexp(n)) => n.eval(ctx).map(|n|          (i.i(), 0b00_110_110, encode(d), n             ).into()),
            Ld8(Reg(A), Blv(BptrBC)) => Ok(                          (       0b00_001_010                           ).into()),
            Ld8(Reg(A), Blv(BptrDE)) => Ok(                          (       0b00_011_010                           ).into()),
            Ld8(Reg(A), Blv(Bptr(nn))) => nn.encode(ctx).map(|(l,h)| (       0b00_111_010, l, h                     ).into()),
            Ld8(BptrBC, Blv(Reg(A))) => Ok(                          (       0b00_000_010                           ).into()),
            Ld8(BptrDE, Blv(Reg(A))) => Ok(                          (       0b00_010_010                           ).into()),
            Ld8(Bptr(nn), Blv(Reg(A))) => nn.encode(ctx).map(|(l,h)| (       0b00_110_010, l, h                     ).into()),
            Ld8(Reg(A), Blv(I)) => Ok(                               (0xED,  0b01_010_111                           ).into()),
            Ld8(Reg(A), Blv(R)) => Ok(                               (0xED,  0b01_011_111                           ).into()),
            Ld8(I, Blv(Reg(A))) => Ok(                               (0xED,  0b01_000_111                           ).into()),
            Ld8(R, Blv(Reg(A))) => Ok(                               (0xED,  0b01_001_111                           ).into()),
            Ld8(_, _) => Err(EncodeError::InvalidInstruction),

            Ld16(lv, Wexp(nn)) => nn.encode(ctx).and_then(|(l, h)| match (lv.try_dd(), lv) {
                (Some(dd), _) => Ok(                                 (       0b00_00_0001 | dd.dd() << 4, l, h      ).into()),
                (_, Ind(i)) => Ok(                                   (i.i(), 0b00_00_0001 | HL.dd() << 4, l, h      ).into()),
                _ => Err(EncodeError::InvalidInstruction),
            }),
            Ld16(lv, Wlv(Wptr(nn))) => nn.encode(ctx).and_then(|(l, h)| match (lv.try_dd(), lv) {
                (Some(HL), _) => Ok(                                 (       0b00_10_1010, l, h                     ).into()),
                (Some(dd), _) => Ok(                                 (0xED,  B_01_DD_1011 | dd.dd() << 4, l, h      ).into()),
                (_, Ind(i)) => Ok(                                   (i.i(), 0b00_10_1010, l, h                     ).into()),
                _ => Err(EncodeError::InvalidInstruction),
            }),
            Ld16(Wptr(nn), rv) => nn.encode(ctx).and_then(|(l, h)| match rv {
                Wlv(Pair2(HL)) => Ok(                                (       0b00_10_0010, l, h                     ).into()),
                Wlv(Pair2(dd)) => Ok(                                (0xED,  B_01_DD_0011 | dd.dd() << 4, l, h      ).into()),
                Wlv(Ind(i)) => Ok(                                   (i.i(), 0b00_10_0010, l, h                     ).into()),
                _ => Err(EncodeError::InvalidInstruction),
            }),
            Ld16(Pair2(SP), Wlv(Pair2(HL))) => Ok(                   (       0b11_00_1001 | SP.dd() << 4            ).into()),
            Ld16(Pair2(SP), Wlv(Ind(i))) => Ok(                      (i.i(), 0b11_00_1001 | SP.dd() << 4            ).into()),
            Ld16(_, _) => Err(EncodeError::InvalidInstruction),

            Push(Wlv(Pair1(qq))) => Ok(                              (       0b11_00_0101 | qq.qq() << 4            ).into()),
            Push(Wlv(Ind(i))) => Ok(                                 (i.i(), 0b11_00_0101 | HL.dd() << 4            ).into()),
            Push(_) => Err(EncodeError::InvalidInstruction),
            Pop(Pair1(qq)) => Ok(                                    (       0b11_00_0001 | qq.qq() << 4            ).into()),
            Pop(Ind(i)) => Ok(                                       (i.i(), 0b11_00_0001 | HL.dd() << 4            ).into()),
            Pop(_) => Err(EncodeError::InvalidInstruction),
                
            Nop => Ok(                                               (       0b00000000                             ).into()),
            Halt => Ok(                                              (       0b01110110                             ).into()),
            Di => Ok(                                                (       0b11110011                             ).into()),
            Ei => Ok(                                                (       0b11111011                             ).into()),
            Im0 => Ok(                                               (0xED,  0b01000110                             ).into()),
            Im1 => Ok(                                               (0xED,  0b01010110                             ).into()),
            Im2 => Ok(                                               (0xED,  0b01011110                             ).into()),

            Inc16(w) => match (w.try_ss(), w) {
                (Some(ss), _) => Ok(                                 (       B_00_SS_0011 | ss.ss() << 4            ).into()),
                (_, Ind(i)) => Ok(                                   (i.i(), B_00_SS_0011 | HL.ss() << 4            ).into()),
                _ => Err(EncodeError::InvalidInstruction),
            },
            Dec16(w) => match (w.try_ss(), w) {
                (Some(ss), _) => Ok(                                 (       B_00_SS_1011 | ss.ss() << 4            ).into()),
                (_, Ind(i)) => Ok(                                   (i.i(), B_00_SS_1011 | HL.ss() << 4            ).into()),
                _ => Err(EncodeError::InvalidInstruction),
            },
            
            Jp(j) => j.encode_abs(addr, ctx).map(|(l, h)|            (       0b11_000_011, l, h                     ).into()),
            JpIf(cc, j) => j.encode_abs(addr, ctx).map(|(l, h)|      (       B_11_CCC_010 | cc.cc() << 3, l, h      ).into()),
            Jr(j) => j.encode_rel(addr, ctx).map(|e2|                (       0b00_011_000, e2                       ).into()),
            JrIf(cc, j) => j.encode_rel(addr, ctx).and_then(|e2| match cc {
                Condition::C => Ok(                                  (       0b00_111_000, e2                       ).into()),
                Condition::NC => Ok(                                 (       0b00_110_000, e2                       ).into()),
                Condition::Z => Ok(                                  (       0b00_101_000, e2                       ).into()),
                Condition::NZ => Ok(                                 (       0b00_100_000, e2                       ).into()),
                _ => Err(EncodeError::InvalidInstruction),
            }),
            Jp(JumpTarget::HL) => Ok(                                (       0b11_101_001                           ).into()),
            Jp(JumpTarget::Ind(i)) => Ok(                            (i.i(), 0b11_101_001                           ).into()),
            Djnz(j) => j.encode_rel(addr, ctx).map(|e2|              (       0b00_010_000, e2                       ).into()),
            
            Call(j) => j.encode_abs(addr, ctx).map(|(l, h)|          (       0b11_001_101, l, h                     ).into()),
            CallIf(cc, j) => j.encode_abs(addr, ctx).map(|(l, h)|    (       B_11_CCC_100 | cc.cc() << 3, l, h      ).into()),
            Ret => Ok(                                               (       0b11_001_001                           ).into()),
            RetIf(cc) => Ok(                                         (       B_11_CCC_000 | cc.cc() << 3            ).into()),
            Reti => Ok(                                              (0xED,  0b01001101                             ).into()),
            Retn => Ok(                                              (0xED,  0b01000101                             ).into()),
            Rst(p) => Ok(                                            (       B_11_TTT_111 | p.p()                   ).into()),
            Out(Bexp(n), Blv(Reg(A))) => n.eval(ctx).map(|n|         (       0b11010011, n                          ).into()),
            Out(Blv(Reg(C)), Blv(Reg(r))) => Ok(                     (0xED,  B_01_RRR_001 | r.r() << 3              ).into()),
            Out(_, _) => Err(EncodeError::InvalidInstruction),

            Daa|Cpl|Neg|Ccf|Scf => unimplemented!(),

/*
            LdXrXn(r, n) => n.encode(bcs, ls).map(|n| (0b00_000_110 | (r.r() << 3), n).into()),
            LdIA => Ok((0xED, 0x47).into()),
            PushXqq(qq) => Ok((0b11_00_0101 | (qq.qq() << 4)).into()),
            PushXii(ii) => Ok(ii.prefix_code( (0xE5).into() )),
            PopXqq(qq) => Ok((0b11_00_0001 | (qq.qq() << 4)).into()),
            PopXii(ii) => Ok(ii.prefix_code( (0xE1).into() )),
            //Dec(r) => Ok((0b00_000_101 | (r.r() << 3)).into()),
            JrXe(j) => j.encode_rel(addr, ls).map(|e2| (0x18, e2).into()),
            JrNzXe(j) => j.encode_rel(addr, ls).map(|e2| (0x20, e2).into()),
            DjnzXe(j) => j.encode_rel(addr, ls).map(|e2| (0x10, e2).into()),
            CallXnn(j) => j.encode_abs(addr, ls).map(|(l, h)| (0xCD, l, h).into()),
            Ret => Ok((0xC9).into()),
            Reti => Ok((0xED, 0x4D).into()),
            OutPnA(n) => n.encode(bcs, ls).map(|n| (0xD3, n).into()),
            OutPCXr(r) => Ok((0xED, 0b01_000_001 | (r.r() << 3)).into()),
*/
        }
    }

    fn tstates(self) -> TStates {
        use Instruction::*;
        use TStates::*;
        match self {
            DbXn(_) | DwXnn(_) => Never,
            _ => Never,
            /*
            LdXrXn(_, _) => Always(&[4, 3]),
            LdIA => Always(&[4, 5]),
            PushXqq(_) => Always(&[5, 3, 3]),
            PushXii(ii) => ii.prefix_tstates(&[5, 3, 3]),
            PopXqq(_) => Always(&[4, 3, 3]),
            PopXii(ii) => ii.prefix_tstates(&[4, 3, 3]),

            AddAXs(s) => s.tstates(),
            AdcAXs(s) => s.tstates(),
            SubXs(s) => s.tstates(),
            SbcAXs(s) => s.tstates(),
            AndXs(s) => s.tstates(),
            OrXs(s) => s.tstates(),
            XorXs(s) => s.tstates(),
            CpXs(s) => s.tstates(),
            IncXm(m) => m.tstates(),
            DecXm(m) => m.tstates(),

            Nop|Halt|Di|Ei => Always(&[4]),
            Im0|Im1|Im2 => Always(&[4, 4]),
            JrXe(_) => Always(&[4, 3, 5]),
            JrNzXe(_) => Either(&[4, 3, 5], &[4, 3]),
            DjnzXe(_) => Either(&[5, 3, 5], &[5, 3]),
            CallXnn(_) => Always(&[4, 3, 4, 3, 3]),
            Ret => Always(&[4, 3, 3]),
            Reti => Always(&[4, 4, 3, 3]),
            OutPnA(_) => Always(&[4, 3, 4]),
            OutPCXr(_) => Always(&[4, 4, 4]),
*/
        }
    }

    fn mnemonic(self) -> String {
        use Instruction::*;
        match self {
            DbXn(n) => format!(".DB {}", n.mnemonic()),
            DwXnn(nn) => format!(".DW {}", nn.mnemonic()),

            Ld8(lv, rv) => format!("LD {}, {}", lv.mnemonic(), rv.mnemonic()),
            Ld16(lv, rv) => format!("LD {}, {}", lv.mnemonic(), rv.mnemonic()),
            Push(rv) => format!("PUSH {}", rv.mnemonic()),
            Pop(lv) => format!("POP {}", lv.mnemonic()),

/*          
            LdXrXr(r, r1) => format!("LD {}, {}", r.mnemonic(), r1.mnemonic()),
            LdXrXn(r, n) =>  format!("LD {}, {}", r.mnemonic(), n.mnemonic()),
            LdXrPHL(r) =>       format!("LD {}, (HL)", r.mnemonic()),
            LdXrPid(r, i, d) => format!("LD {}, ({}+{})", r.mnemonic(), i.mnemonic(), d),
            LdPHLXr(r) =>       format!("LD (HL), {}", r.mnemonic()),
            LdPidXr(i, d, r) => format!("LD ({}+{}), {}", i.mnemonic(), d, r.mnemonic()),
            LdPHLXn(n) =>       format!("LD (HL), {}", n.mnemonic()),
            LdPidXn(i, d, n) => format!("LD ({}+{}), {}", i.mnemonic(), d, n.mnemonic()),
            LdAPBC => format!("LD A, (BC)"),
            LdAPDE => format!("LD A, (DE)"),
            LdAPnn(nn) => format!("LD A, ({})", nn.mnemonic()),
            LdPBCA => format!("LD (BC), A"),
            LdPDEA => format!("LD (DE), A"),
            LdPnnA(nn) => format!("LD ({}), A", nn.mnemonic()),
            LdAI => format!("LD A, I"),
            LdAR => format!("LD A, R"),
            LdIA => format!("LD I, A"),
            LdRA => format!("LD R, A"),

            LdXddXnn(dd, nn) => format!("LD {}, {}", dd.mnemonic(), nn.mnemonic()),
            LdXiiXnn(ii, nn) => format!("LD {}, {}", ii.mnemonic(), nn.mnemonic()),
            LdXddPnn(dd, nn) => format!("LD {}, ({})", dd.mnemonic(), nn.mnemonic()),
            LdXiiPnn(ii, nn) => format!("LD {}, ({})", ii.mnemonic(), nn.mnemonic()),
            LdPnnXdd(nn, dd) => format!("LD ({}), {}", nn.mnemonic(), dd.mnemonic()),
            LdPnnXii(nn, ii) => format!("LD ({}), {}", nn.mnemonic(), ii.mnemonic()),
            LdSPXii(ii) => format!("LD SP, {}", ii.mnemonic()),
            PushXqq(qq) => format!("PUSH {}", qq.mnemonic()),
            PushXii(ii) => format!("PUSH {}", ii.mnemonic()),
            PopXqq(qq) => format!("POP {}", qq.mnemonic()),
            PopXii(ii) => format!("POP {}", ii.mnemonic()),

            ExDEHL => format!("EX DE, HL"),
            ExAFAF => format!("EX AF, AF'"),
            Exx => format!("EXX"),
            ExPSPXii(ii) => format!("EX (SP), {}", ii.mnemonic()),
            Ldi => format!("LDI"),
            Ldir => format!("LDIR"),
            Ldd => format!("LDD"),
            Lddr => format!("LDDR"),
            Cpi => format!("CPI"),
            Cpir => format!("CPIR"),
            Cpd => format!("CPD"),
            Cpdr => format!("CPDR"),
*/
            Daa => "DAA".to_owned(),
            Cpl => "CPL".to_owned(),
            Neg => "NEG".to_owned(),
            Ccf => "CCF".to_owned(),
            Scf => "SCF".to_owned(),
            Nop => "NOP".to_owned(),
            Halt => "HALT".to_owned(),
            Di => "DI".to_owned(),
            Ei => "EI".to_owned(),
            Im0 => "IM 0".to_owned(),
            Im1 => "IM 1".to_owned(),
            Im2 => "IM 2".to_owned(),
/*
            AddAXs(s) => format!("ADD A, {}", s.mnemonic()),
            AdcAXs(s) => format!("ADC A, {}", s.mnemonic()),
            SubXs(s) => format!("SUB {}", s.mnemonic()),
            SbcAXs(s) => format!("SBC A, {}", s.mnemonic()),
            AndXs(s) => format!("AND {}", s.mnemonic()),
            OrXs(s) => format!("OR {}", s.mnemonic()),
            XorXs(s) => format!("XOR {}", s.mnemonic()),
            CpXs(s) => format!("CP {}", s.mnemonic()),
            IncXm(m) => format!("INC {}", m.mnemonic()),
            DecXm(m) => format!("DEC {}", m.mnemonic()),

            AddHLXss(ss) => format!("ADD HL, {}", ss.mnemonic()),
            AdcHLXss(ss) => format!("ADC HL, {}", ss.mnemonic()),
            SbcHLXss(ss) => format!("SBC HL, {}", ss.mnemonic()),
            AddIXXpp(pp) => format!("ADD IX, {}", pp.mnemonic()),
            AddIYXrr(rr) => format!("ADD IY, {}", rr.mnemonic()),
            IncXss(ss) => format!("INC {}", ss.mnemonic()),
            IncXi(i) => format!("INC {}", i.mnemonic()),
            DecXss(ss) => format!("DEC {}", ss.mnemonic()),
            DecXi(i) => format!("DEC {}", i.mnemonic()),

            JrXe(j) => format!("JR {}", j.mnemonic()),
            JrNzXe(j) => format!("JR NZ, {}", j.mnemonic()),
            DjnzXe(j) => format!("DJNZ {}", j.mnemonic()),
            CallXnn(j) => format!("CALL {}", j.mnemonic()),
*/

            Inc16(lv) => format!("INC {}", lv.mnemonic()),
            Dec16(lv) => format!("DEC {}", lv.mnemonic()),
            
            Jp(j) => format!("JP {}", j.mnemonic()),
            JpIf(cc, j) => format!("JP {}, {}", cc.mnemonic(), j.mnemonic()),
            Jr(j) => format!("JR {}", j.mnemonic()),
            JrIf(cc, j) => format!("JR {}, {}", cc.mnemonic(), j.mnemonic()),
            Djnz(j) => format!("DJNZ {}", j.mnemonic()),
            
            Call(j) => format!("CALL {}", j.mnemonic()),
            CallIf(cc, j) => format!("CALL {}, {}", cc.mnemonic(), j.mnemonic()),
            Ret => "RET".to_owned(),
            RetIf(cc) => format!("RET {}", cc.mnemonic()),
            Reti => "RETI".to_owned(),
            Retn => "RETN".to_owned(),
            Rst(p) => format!("RST {}", p.mnemonic()),
/*
            OutPnA(n) => format!("OUT ({}), A", n.mnemonic()),
            OutPCXr(r) => format!("OUT (C), {}", r.mnemonic()),
*/
            Out(rv1, rv2) => format!("OUT ({}), {}", rv1.mnemonic(), rv2.mnemonic()),
        }
    }
}

// `j` custom (`nn` or `e` or HL/IX/IY, note wrong JP (HL) mnemonic in manual)
#[derive(Clone, Copy, Debug, PartialEq)]
enum JumpTarget<'a> {
    Label(&'a str),
    Relative(isize), // -126..+129
    HL,
    Ind(IndexRegister),
}

impl<'a> JumpTarget<'a> {
    fn mnemonic(self) -> String {
        use JumpTarget::*;
        match self {
            Label(s) => format!("@{}", s),
            Relative(0) => "@".to_owned(),
            Relative(x) if x > 0 => format!("@+{}", x),
            Relative(x) => format!("@-{}", -x),
            HL => "HL".to_owned(),
            Ind(i) => i.mnemonic().to_owned(),
        }
    }

    fn encode_rel(
        self, addr: usize, ctx: &dyn Lookup
    ) -> Result<u8, EncodeError> {
        use JumpTarget::*;
        match self { // NOTE: jump from addr+2
            Label(l) => ctx.label2addr(l).and_then(|a| addr2rel(a, addr+2)),
            Relative(r) => Ok((r-2) as i8),
            _ => Err(EncodeError::InvalidInstruction),
        }
        .map(|i| i.to_le_bytes()[0])
    }

    fn encode_abs(
        self, addr: usize, ctx: &dyn Lookup
    ) -> Result<(u8, u8), EncodeError> {
        use JumpTarget::*;
        match self {
            Label(l) => ctx.label2addr(l),
            Relative(r) => if r >= 0 {
                Ok(addr + (r as usize))
            } else {
                Ok(addr - ((-r) as usize))
            },
            _ => Err(EncodeError::InvalidInstruction),
        }
        .map(|u| { let s = u.to_le_bytes(); (s[0], s[1]) })
    }
}

fn print_listing(
    org: usize, is: &[(Vec<&str>, Instruction)], lookup: &TrueLookup
) -> Vec<u8> {
    let mut offs = 0;
    let mut res = vec![];

    for (ls, i) in is {
        let addr = org+offs;
        match i.encode(addr, lookup) {
            Ok(code) => {
                res.extend_from_slice(code.bytes());
                let bytes = format!("{:02X?}", code.bytes());

                println!(
                    "{:>04X}: {:15}{:>20}{:20}; {:?}",
                    addr,
                    bytes,
                    ls.iter().map(|l| format!("@{}: ", l))
                        .fold("".to_owned(), |mut acc, x| {acc.push_str(&x); acc}),
                    i.mnemonic(),
                    i.tstates()
                );
                offs += code.len;
            },
            Err(e) => {
                println!("ERROR: {:?}", e);
                break
            }
        }
    }
    res
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Directive<'a> {
    Org(usize),
    Equ8(&'a str, ByteExpr<'a>),
    Equ16(&'a str, WordExpr<'a>),
    Label(&'a str),
    Emit(Instruction<'a>),
    Align(usize, usize),
    Fill(Instruction<'a>, usize),
}

impl<'t> Directive<'t> {
    fn advance(&self, cur: usize) -> Result<usize, EncodeError> {
        use Directive::*;
        match self {
            &Org(n) => Ok(n),
            &Equ8(_, _) | &Equ16(_, _) | &Label(_) => Ok(cur),
            &Emit(i) => i.length().map(|l| l + cur),
            &Align(0, n) => Ok(n + cur),
            &Align(m, n) => Ok((cur / m + if cur % m > n {1} else {0}) * m + n),
            &Fill(i, n) => i.length().map(|l| n*l + cur),
        }
    }
}

use nom::bytes::complete::{tag, is_a, take_while1};
use nom::branch::alt;
use nom::combinator::{cut, map, map_parser, opt, value};
use nom::character::complete::{space0, space1, digit1, hex_digit1, line_ending, not_line_ending};
use nom::sequence::{preceded, tuple};
use nom::AsChar;

fn parse_ident_str(i: &str) -> nom::IResult<&str, &str> {
    take_while1(|c: char| c.is_alphanum() || c == '_')(i)
}

fn parse_comment_str(i: &str) -> nom::IResult<&str, &str> {
    preceded(tag(";"), not_line_ending)(i)
}

fn parse_label_str(i: &str) -> nom::IResult<&str, &str> {
    preceded(tag("@"), parse_ident_str)(i)
}

fn parse_jump_target(i: &str) -> nom::IResult<&str, JumpTarget> {
    alt((
        map(parse_label_str, JumpTarget::Label),
        map(
            tuple( (tag("@"), space0, parse_displacement) ),
            |(_, _, d)| JumpTarget::Relative(d)
        ), // TODO isize/i8
        value(JumpTarget::HL, tag("HL")),
        map(parse_index_register, JumpTarget::Ind),
    ))(i)
}
/*
enum InstructionMnemonic {
    Db, Dw,
    Ld, Push, Pop,
    Nop, Ei, Di, Halt, Reti, Retn, Ret, Im,
    Inc, Dec,
    Jr, Djnz, Call,
    Out
}

static INSTRUCTION_MAP: phf::Map<&'static str, InstructionMnemonic> = phf_map! {
    ".DB" => InstructionMnemonic::Db,
    ".DW" => InstructionMnemonic::Dw,
    "LD" => InstructionMnemonic::Ld,
    "PUSH" => InstructionMnemonic::Push,
    "POP" => InstructionMnemonic::Pop,
    "NOP" => InstructionMnemonic::Nop,
    "EI" => InstructionMnemonic::Ei,
    "DI" => InstructionMnemonic::Di,
    "HALT" => InstructionMnemonic::Halt,
    "RETI" => InstructionMnemonic::Reti,
    "RETN" => InstructionMnemonic::Retn,
    "RET" => InstructionMnemonic::Ret,
    "IM" => InstructionMnemonic::Im,
    "INC" => InstructionMnemonic::Inc,
    "DEC" => InstructionMnemonic::Dec,
    "JR" => InstructionMnemonic::Jr,
    "DJNZ" => InstructionMnemonic::Djnz,
    "CALL" => InstructionMnemonic::Call,
    "OUT" => InstructionMnemonic::Out,
}

fn parse_instruction_mnemonic(i: &str) -> nom::IResult<&str, InstructionMnemonic> {
    take_while1(|c: char| c.is_alpha() || c == '.')(i)
}
*/
fn parse_instruction(i: &str) -> nom::IResult<&str, Instruction> {
    alt((
        alt((
            parse_unary_op(".DB", parse_byte_expr, Instruction::DbXn),
            parse_unary_op(".DW", parse_word_expr, Instruction::DwXnn),
        )),
        parse_binary_op("LD", parse_byte_lv, parse_byte_rv, Instruction::Ld8),
        parse_binary_op("LD", parse_word_lv, parse_word_rv, Instruction::Ld16),
        parse_unary_op("PUSH", parse_word_rv, Instruction::Push),
        parse_unary_op("POP", parse_word_lv, Instruction::Pop),
        alt((
            map(tag("NOP"), |_| Instruction::Nop),
            map(tag("EI"), |_| Instruction::Ei),
            map(tag("DI"), |_| Instruction::Di),
            map(tag("HALT"), |_| Instruction::Halt),
            map(tag("RETI"), |_| Instruction::Reti),
            map(tag("RETN"), |_| Instruction::Retn),
            map(tag("RET"), |_| Instruction::Ret),
        )),
        map(tuple( (tag("IM"), space1, tag("0")) ), |_| Instruction::Im0),
        map(tuple( (tag("IM"), space1, tag("1")) ), |_| Instruction::Im1),
        map(tuple( (tag("IM"), space1, tag("2")) ), |_| Instruction::Im2),
        parse_unary_op("INC", parse_word_lv, Instruction::Inc16),
        parse_unary_op("DEC", parse_word_lv, Instruction::Dec16),
        parse_unary_op("JR", parse_jump_target, Instruction::Jr),
        parse_unary_op("DJNZ", parse_jump_target, Instruction::Djnz),
        parse_unary_op("CALL", parse_jump_target, Instruction::Call),
        parse_binary_op("OUT", parse_surrounded("(", parse_byte_rv, ")"), parse_byte_rv, Instruction::Out),
    ))(i)
}

fn parse_usize(i: &str) -> nom::IResult<&str, usize> {
    // TODO: overflow/unwrap
    alt((
        map(tuple( (tag("#"), hex_digit1) ), |(_, hs)| usize::from_str_radix(hs, 16).unwrap()),
        map(tuple( (tag("%"), is_a("01")) ), |(_, bs)| usize::from_str_radix(bs, 2).unwrap()),
        map(digit1, |ds: &str| ds.parse::<usize>().unwrap()),
    ))(i)
}

fn parse_byte(i: &str) -> nom::IResult<&str, u8> {
    // TODO: overflow/unwrap
    alt((
        map(tuple( (tag("#"), hex_digit1) ), |(_, hs)| u8::from_str_radix(hs, 16).unwrap()),
        map(tuple( (tag("%"), is_a("01")) ), |(_, bs)| u8::from_str_radix(bs, 2).unwrap()),
        map(digit1, |ds: &str| ds.parse::<u8>().unwrap()),
    ))(i)
}

fn parse_word(i: &str) -> nom::IResult<&str, u16> {
    // TODO: overflow/unwrap
    alt((
        map(tuple( (tag("#"), hex_digit1) ), |(_, hs)| u16::from_str_radix(hs, 16).unwrap()),
        map(tuple( (tag("%"), is_a("01")) ), |(_, bs)| u16::from_str_radix(bs, 2).unwrap()),
        map(digit1, |ds: &str| ds.parse::<u16>().unwrap()),
    ))(i)
}

fn parse_displacement(i: &str) -> nom::IResult<&str, isize> {
    // TODO: correct +/-
    alt((
        map(tuple( (tag("+"), space0, parse_usize) ), |(_, _, d)| d as isize),
        map(tuple( (tag("-"), space0, parse_usize) ), |(_, _, d)| -(d as isize)),
    ))(i)
}

fn parse_byte_expr(i: &str) -> nom::IResult<&str, ByteExpr> {
    alt((
        map(parse_byte, ByteExpr::Immediate),
        map(preceded(tag("$"), parse_ident_str), ByteExpr::Const),
        map(tuple( (tag("!hi("), space0, parse_label_str, space0, tag(")")) ), |(_,_, l, _,_)| ByteExpr::LabelHi(l)),
        map(tuple( (tag("!lo("), space0, parse_label_str, space0, tag(")")) ), |(_,_, l, _,_)| ByteExpr::LabelLo(l)),
    ))(i)
}

fn parse_word_expr(i: &str) -> nom::IResult<&str, WordExpr> {
    alt((
        map(parse_word, WordExpr::Immediate),
        map(tuple( (parse_byte_expr, tag(":"), parse_byte_expr) ), |(h, _, l)| WordExpr::HiLo(h, l)),
        map(preceded(tag("$$"), parse_ident_str), WordExpr::Const),
        map(parse_label_str, WordExpr::Label),
    ))(i)
}

fn parse_register(i: &str) -> nom::IResult<&str, Register> {
    alt((
        value(Register::A, tag("A")),
        value(Register::B, tag("B")),
        value(Register::C, tag("C")),
        value(Register::D, tag("D")),
        value(Register::E, tag("E")),
        value(Register::H, tag("H")),
        value(Register::L, tag("L")),
    ))(i)
}

fn parse_register_pair1(i: &str) -> nom::IResult<&str, RegisterPair1> {
    alt((
        value(RegisterPair1::BC, tag("BC")),
        value(RegisterPair1::DE, tag("DE")),
        value(RegisterPair1::HL, tag("HL")),
        value(RegisterPair1::AF, tag("AF")),
    ))(i)
}

fn parse_register_pair2(i: &str) -> nom::IResult<&str, RegisterPair2> {
    alt((
        value(RegisterPair2::BC, tag("BC")),
        value(RegisterPair2::DE, tag("DE")),
        value(RegisterPair2::HL, tag("HL")),
        value(RegisterPair2::SP, tag("SP")),
    ))(i)
}

fn parse_index_register(i: &str) -> nom::IResult<&str, IndexRegister> {
    alt((
        value(IndexRegister::IX, tag("IX")),
        value(IndexRegister::IY, tag("IY")),
    ))(i)
}

fn parse_word_lv(i: &str) -> nom::IResult<&str, WordLv> {
    alt((
        map(parse_register_pair1, WordLv::Pair1),
        map(parse_register_pair2, WordLv::Pair2),
        map(parse_index_register, WordLv::Ind),
        map(parse_surrounded("(", parse_word_expr, ")"), WordLv::Wptr),
    ))(i)
}

fn parse_word_rv(i: &str) -> nom::IResult<&str, WordRv> {
    alt((
        map(parse_word_expr, WordRv::Wexp),
        map(parse_word_lv, WordRv::Wlv),
    ))(i)
}

fn parse_byte_lv(i: &str) -> nom::IResult<&str, ByteLv> {
    alt((
        map(parse_register, ByteLv::Reg),
        value(ByteLv::R, tag("R")),
        value(ByteLv::I, tag("I")),
        value(ByteLv::BptrHL, tag("(HL)")), // TODO: need this?
        map(
            parse_surrounded("(", tuple((parse_index_register, space0, parse_displacement)), ")"),
            |(i, _, d)| ByteLv::Bdsp(i, d as i8),
        ),
        value(ByteLv::BptrBC, tag("(BC)")), // TODO: need this?
        value(ByteLv::BptrDE, tag("(DE)")), // TODO: need this?
        map(parse_surrounded("(", parse_word_expr, ")"), ByteLv::Bptr),
    ))(i)
}

fn parse_byte_rv(i: &str) -> nom::IResult<&str, ByteRv> {
    alt((
        map(parse_byte_expr, ByteRv::Bexp),
        map(parse_byte_lv, ByteRv::Blv),
    ))(i)
}

fn parse_surrounded<'t, O, F>(
    b: &'t str, f: F, e: &'t str
) -> impl FnMut(&'t str) -> nom::IResult<&'t str, O>
where F: FnMut(&'t str) -> nom::IResult<&'t str, O>
{
    map(
        tuple( (tag(b), space0, f, space0, tag(e)) ),
        |(_, _, o, _, _)| o,
    )
}

fn parse_unary_op<'t, O, A1, F1, MF>(
    t: &'t str, f1: F1, mf: MF
) -> impl FnMut(&'t str) -> nom::IResult<&'t str, O>
where
    F1: FnMut(&'t str) -> nom::IResult<&'t str, A1>,
    MF: Fn(A1) -> O,
{
    map(
        tuple( (tag(t), space1, f1) ),
        move |(_, _, a1)| mf(a1)
    )
}

fn parse_binary_op<'t, O, A1, A2, F1, F2, MF>(
    t: &'t str, f1: F1, f2: F2, mf: MF
) -> impl FnMut(&'t str) -> nom::IResult<&'t str, O>
where
    F1: FnMut(&'t str) -> nom::IResult<&'t str, A1>,
    F2: FnMut(&'t str) -> nom::IResult<&'t str, A2>,
    MF: Fn(A1, A2) -> O,
{
    map(
        tuple((
            tag(t), space1,
            f1, space0,
            tag(","), space0,
            f2
        )),
        move |(_, _, a1, _, _, _, a2)| mf(a1, a2)
    )
}
                                            
fn parse_directive(i: &str) -> nom::IResult<&str, Directive> {
    alt((
        parse_unary_op(".ORG", parse_usize, Directive::Org),
        parse_binary_op(".EQU", preceded(tag("$"), parse_ident_str), parse_byte_expr, Directive::Equ8),
        parse_binary_op(".EQU", preceded(tag("$$"), parse_ident_str), parse_word_expr, Directive::Equ16),
        map(tuple((parse_label_str, space0, tag(":"))), |(l, _, _)| Directive::Label(l)),
        map(parse_instruction, Directive::Emit),
        parse_binary_op(".ALIGN", parse_usize, parse_usize, Directive::Align),
        parse_binary_op(".FILL", parse_surrounded("`", parse_instruction, "`"), parse_usize, Directive::Fill),
    ))(i)
}

fn parse_line(i: &str) -> nom::IResult<&str, Option<Directive>> {
    map(
        tuple((
            space0,
            opt(parse_directive),
            space0,
            opt(parse_comment_str),
            line_ending,
        )),
        |(_, d, _, _, _)| d
    )(i)
}

fn parse(i: &str) -> nom::IResult<&str, Vec<Directive>> {
    nom::multi::fold_many0(
        parse_line,
        Vec::new(),
        |mut acc, opt_d| {
            if let Some(d) = opt_d {
                acc.push(d);
            }
            acc
        }
    )(i)
}

#[derive(Debug)]
enum ResolveError<'a> {
    AdvanceError(EncodeError),
    EquFailure(EncodeError),
    LabelRedefinition(&'a str),
}

fn resolve<'a>(ds: &[Directive<'a>]) ->
    Result<(usize, Vec<(Vec::<&'a str>, Instruction<'a>)>, TrueLookup<'a>), ResolveError<'a>>
{
    let mut lookup = TrueLookup::new();
    let mut is = vec![];
    let mut addr = 0;
    let mut org = None;
    let mut lacc = vec![];
    for d in ds {
        use Directive::*;
        match d.advance(addr) {
            Err(e) => {
                println!("error in {:?}", d);
                return Err(ResolveError::AdvanceError(e))
            },
            Ok(mut nextaddr) => {
                match d {
                    Org(p) => nextaddr = *p,
                    Equ8(c, bexp) => match bexp.eval(&lookup) { // allow overriding
                        Ok(b) => { lookup.byte_consts.insert(*c, b); },
                        Err(e) => return Err(ResolveError::EquFailure(e)),
                    },
                    Equ16(c, wexp) => match wexp.eval(&lookup) { // allow overriding
                        Ok(w) => { lookup.word_consts.insert(*c, w); },
                        Err(e) => return Err(ResolveError::EquFailure(e)),
                    },
                    Label(l) => if lookup.labels.get(l).is_some() {
                        return Err(ResolveError::LabelRedefinition(*l));
                    } else {
                        lookup.labels.insert(*l, addr);
                        lacc.push(*l);
                    },
                    Emit(i) => {
                        is.push((lacc, *i));
                        lacc = vec![];
                    }
                    Align(_, _) => for _ in addr..nextaddr {
                        is.push((vec![], Instruction::Nop));
                    },
                    Fill(i, n) => for _ in 0..*n {
                        is.push((lacc, *i));
                        lacc = vec![];
                    },
                }
                addr = nextaddr;
                org.get_or_insert(addr);
            }
        }
    }
    Ok((org.unwrap_or(0), is, lookup))
}

use std::io::{Write, Read};

fn save_bin(filename: &str, bytes: &[u8]) {
    std::fs::File::create(filename)
        .and_then(|mut f| f.write_all(bytes))
        .unwrap();
}

#[derive(Debug)]
struct TapFile {
    pairs: Vec<TapBlockPair>,
}

#[derive(Debug)]
struct ExtraBlock(u8, Bytes);

#[derive(Debug)]
struct TapBlockPair {
    filename: String,
    content: Content,
    extrablocks: Vec<ExtraBlock>,
    derived_total_length: usize,
}

fn write_file(filename: &str, bs: &[u8]) -> Result<(), String> {
    std::fs::File::create(filename)
        .and_then(|mut f| f.write_all(bs))
        .map_err(|e| e.to_string())
}

trait Tag {
    fn mismatch() -> Self;
    fn print_byte(o: &mut String, b: u8, a: &Self);
}

use std::fmt::Write as FmtWrite;

impl Tag for Plus3DosTag {
    fn mismatch() -> Self {
        Plus3DosTag::Mismatch
    }
    fn print_byte(o: &mut String, b: u8, a: &Plus3DosTag) {
        use Plus3DosTag::*;
        use termion::color::*;
        match a {
            Magic => write!(o, " {}{}{:02X}{}{}", Fg(Red), Bg(Black), b, Reset.bg_str(), Reset.fg_str()),
            Checksum => write!(o, " {}{}{:02X}{}{}", Fg(LightRed), Bg(Black), b, Reset.bg_str(), Reset.fg_str()),
            Basic(bt) => Ok(print_byte(o, b, bt)),
            Unknown  => write!(o, " {:02X}", b),
            Mismatch => write!(o, " {}{:02X}{}", Fg(LightRed), b, Reset.fg_str()), // TODO:
        }.unwrap()
    }
}

fn print_byte(o: &mut String, b: u8, a: &BasicTag) {
    use BasicTag::*;
    use termion::color::*;
    match *a {
        Keyword => write!(o, " {}{}{:02X}{}{}", Fg(Green), Bg(Black), b, Reset.bg_str(), Reset.fg_str()),
        Number => write!(o, " {}{}{:02X}{}{}", Fg(Blue), Bg(Black), b, Reset.bg_str(), Reset.fg_str()),
        VarHead => write!(o, " {}{}{:02X}{}{}", Fg(Yellow), Bg(Black), b, Reset.bg_str(), Reset.fg_str()),
        VarTail => write!(o, " {}{}{:02X}{}{}", Fg(Yellow), Bg(Black), b, Reset.bg_str(), Reset.fg_str()),
        LineNumber => write!(o, " {}{}{:02X}{}{}", Fg(LightBlack), Bg(Black), b, Reset.bg_str(), Reset.fg_str()),
        DataLength => write!(o, " {}{}{:02X}{}{}", Fg(Black), Bg(LightBlack), b, Reset.bg_str(), Reset.fg_str()),
        Unknown => write!(o, " {:02X}", b),
    }.unwrap()
}

impl Tag for TapTag {
    fn mismatch() -> Self {
        TapTag::Mismatch
    }
    fn print_byte(o: &mut String, b: u8, a: &TapTag) {
        use TapTag::*;
        use termion::color::*;
        match a {
            Basic(bt) => Ok(print_byte(o, b, bt)),
            Unknown => write!(o, " {:02X}", b),
            Mismatch => write!(o, " {}{:02X}{}", Fg(LightRed), b, Reset.fg_str()), // TODO:
            BlockStart => write!(o, " {}{}{:02X}{}{}", Fg(Magenta), Bg(Black), b, Reset.bg_str(), Reset.fg_str()),
            BlockBodyLength => write!(o, " {}{}{:02X}{}{}", Fg(Cyan), Bg(Black), b, Reset.bg_str(), Reset.fg_str()),
            Checksum => write!(o, " {}{}{:02X}{}{}", Fg(Yellow), Bg(Red), b, Reset.bg_str(), Reset.fg_str()),
        }.unwrap()
    }
}

fn print_annotated_split<A: Tag + Default>(ori: &[u8], buf: &AnnotatedBuf<A>) -> (usize, String) {
    let mut o = String::new();
    let mut pos: usize = 0;
    let mut mismatches: usize = 0;
    for (n, a) in buf.attrs.iter() {
        for i in pos..pos+n {
            if i % 16 == 0 {
                write!(&mut o, "\n{:04X}: ", i);
                let mut different = false;
                for j in i..i+16 {
                    if j < ori.len() {
                        if j < buf.bytes.len() && ori[j] == buf.bytes[j] {
                            A::print_byte(&mut o, ori[j], &A::default());
                        } else {
                            different = true;
                            mismatches += 1;
                            A::print_byte(&mut o, ori[j], &A::mismatch());
                        }
                    } else {
                        write!(&mut o, "   ");
                    }
                }
                write!(&mut o, "  {} ", if different { "<>" } else { "==" });
            }
            A::print_byte(&mut o, buf.bytes[i], a);
        }
        pos += n;
    }
    write!(&mut o, "\n");
    (mismatches, o) // NOTE: 0 mismatches if buf is ori + extra
}

fn read_file<T, F>(filename: &str, parser: F) -> Result<(Vec<u8>, T), String>
where
    F: Fn(&[u8]) -> nom::IResult<&[u8], T>,
    T: std::fmt::Debug,
{
    std::fs::File::open(filename)
        .map_err(|e| e.to_string())
        .and_then(|mut f| {
            let mut bytes = Vec::new();
            f.read_to_end(&mut bytes).map(|_sz| bytes).map_err(|e| e.to_string())
        })
        .and_then(|bs| {
            let res = nom::combinator::all_consuming(parser)(&bs);
            match res {
                Ok((_, tap)) => Ok((bs, tap)),
                //Err(nom::Err::Error((i, k))) => Err(format!("offset={}, input={:?}, kind={:?}",
                //                                            i.as_ptr() as usize - bs.as_ptr() as usize, &i[0..10], k)),
                x => Err(format!("{:?}", x)),
            }
        })
}

enum TapTag {
    Unknown, // TODO:
    Basic(BasicTag),
    Mismatch, // TODO:
    BlockStart,
    BlockBodyLength,
    Checksum,
}

impl Default for TapTag {
    fn default() -> Self {
        TapTag::Unknown
    }
}

impl From<BasicTag> for TapTag {
    fn from(t: BasicTag) -> Self {
        TapTag::Basic(t)
    }
}

enum Plus3DosTag {
    Mismatch, // TODO:
    Unknown, // TODO:
    Magic,
    Checksum,
    Basic(BasicTag),
}

impl Default for Plus3DosTag {
    fn default() -> Self {
        Plus3DosTag::Unknown
    }
}

impl From<BasicTag> for Plus3DosTag {
    fn from(t: BasicTag) -> Self {
        Plus3DosTag::Basic(t)
    }
}

enum BasicTag {
    Unknown,
    DataLength,
    Number,
    LineNumber,
    Keyword,
    VarHead,
    VarTail,
}

impl Default for BasicTag {
    fn default() -> Self {
        BasicTag::Unknown
    }
}

struct AnnotatedBuf<A> {
    bytes: Vec<u8>,
    attrs: Vec<(usize, A)>,
}

impl<A: Default> AnnotatedBuf<A> {
    fn new() -> Self {
        Self {
            bytes: Vec::new(),
            attrs: vec![(0, A::default())],
        }
    }
    fn reset<B: Into<A>>(&mut self, attr: B) {
        self.attrs.push((0, attr.into()));
    }
    fn append(&mut self, mut buf: AnnotatedBuf<A>) {
        self.bytes.append(&mut buf.bytes);
        self.attrs.append(&mut buf.attrs);
    }
    fn pad(&mut self, val: u8, count: usize) {
        self.bytes.extend(std::iter::repeat(val).take(count));
        self.attrs.last_mut().unwrap().0 += count;
    }
    fn push(&mut self, byte: u8) {
        self.bytes.push(byte);
        self.attrs.last_mut().unwrap().0 += 1;
    }
    fn extend_from_slice(&mut self, slice: &[u8]) {
        self.bytes.extend_from_slice(slice);
        self.attrs.last_mut().unwrap().0 += slice.len();
    }
    fn update_from_slice(&mut self, offset: usize, slice: &[u8]) {
        self.bytes[offset..offset+slice.len()].copy_from_slice(slice);
    }
    fn len(&self) -> usize {
        self.bytes.len()
    }
}

// https://www.worldofspectrum.org/ZXSpectrum128+3Manual/chapter8pt27.html

#[derive(Debug)]
enum ContentParams {
    Program{autostart: Option<u16>, vars_offset: u16},
    NumberArray{name: char},
    CharacterArray{name: char},
    Code{load_addr: u16, unused: u16},
    Screen{unused: u16},
}

#[derive(Debug)]
struct ContentHeader {
    data_length: u16,
    content_params: ContentParams,
}

impl ContentHeader {
    fn ctag(&self) -> u8 {
        match self.content_params {
            ContentParams::Program{..} => 0x00,
            ContentParams::NumberArray{..} => 0x01,
            ContentParams::CharacterArray{..} => 0x02,
            ContentParams::Code{..} => 0x03,
            ContentParams::Screen{..} => 0x03,
        }
    }
}

#[derive(Debug)]
struct Plus3DosFile {
    issue_number: u8,
    version_number: u8,
    header: ContentHeader,
    content: Content,
}

struct Bytes(Vec<u8>);

impl std::fmt::Debug for Bytes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{} bytes, min={:?}, max={:?}>",
            self.0.len(), self.0.iter().min(), self.0.iter().max()
        )
    }
}

#[derive(Debug)]
enum VarsBlock {
    Ok(Vec<BasicVar>),
    Junk(Bytes),
}

#[derive(Debug)]
enum Content {
    Program{autostart: Option<u16>, lines: Vec<BasicLine>, vars: VarsBlock},
    Code{data: Bytes, addr: u16, unused: u16},
    Screen{bitmap: Bytes, attribs: Bytes, unused: u16}, // 256x192/8 bytes + 32x24 bytes @16384
    NumberArray{name: char, dims: Vec<u16>, values: Vec<BasicNumber>},
    CharacterArray{name: char, dims: Vec<u16>, values: Vec<u8>},
}

use std::convert::TryInto;
use nom::combinator::{verify};
use nom::number::complete::{le_u8, le_u16};

fn plus3dos_parse_content_header(i: &[u8]) -> nom::IResult<&[u8], ContentHeader> {
    let (i, ctag) = verify(le_u8, |x| *x < 4)(i)?;
    let (i, ch) = parse_content_header(i, ctag)?;
    let (i, _) = tag([0])(i)?;
    Ok( (i, ch) )
}

fn plus3dos_unparse_content_header(o: &mut AnnotatedBuf<Plus3DosTag>, header: &ContentHeader) -> Result<(), ContentError> {
    o.push(header.ctag());
    unparse_content_header(o, &header);
    o.push(0x00);
    Ok(())
}

fn plus3dos_parse_file(i: &[u8]) -> nom::IResult<&[u8], Plus3DosFile> {

    let (i, (_, _, issue_number, version_number, data_length, header, _)) =
        map_parser(
            map(
                cut(verify(
                    tuple((
                        nom::bytes::complete::take(127usize),
                        nom::number::complete::be_u8,
                    )),
                    |t: &(&[u8], u8)| t.1 == t.0.iter().fold(0x00u8, |acc, x| acc.wrapping_add(*x))
                )),
                |(bs, _)| bs
            ),
            tuple((
                tag("PLUS3DOS"),
                tag([0x1A]),
                le_u8,
                le_u8,
                map(verify(nom::number::complete::le_u32, |l| *l >= 128), |l| l - 128),
                plus3dos_parse_content_header,
                verify(nom::bytes::complete::take(104usize), |zs: &[u8]| zs.iter().all(|z| *z == 0u8)),
            ))
        )(i)?;

    let (i, content) = map_parser(
        verify(nom::bytes::complete::take(data_length), |x: &[u8]| x.len() == header.data_length as usize),
        nom::combinator::all_consuming(|i| parse_content(&header.content_params, i))
    )(i)?;

    Ok((i, Plus3DosFile{issue_number, version_number, header, content}))
}

fn plus3dos_unparse_file(o: &mut AnnotatedBuf<Plus3DosTag>, p3dos: &Plus3DosFile) -> Result<(), Plus3DosError> {
    o.reset(Plus3DosTag::Magic);
    o.extend_from_slice(b"PLUS3DOS");
    o.push(0x1A);
    o.push(p3dos.issue_number);
    o.push(p3dos.version_number);
    o.reset(Plus3DosTag::Unknown);
    let file_length_offset = o.len();
    o.extend_from_slice(&[0xFF, 0xFF, 0xFF, 0xFF]); // placeholder
    plus3dos_unparse_content_header(o, &p3dos.header);
    o.pad(0x00, 104);
    o.reset(Plus3DosTag::Checksum);
    let checksum_offset = o.len();
    o.push(0xFF); // placeholder
    o.reset(Plus3DosTag::Unknown);
    let content_params = unparse_content(o, &p3dos.content);
    o.update_from_slice(file_length_offset, &(o.len() as u32).to_le_bytes());
    o.update_from_slice(checksum_offset, &[o.bytes[0..checksum_offset].iter().fold(0x00, |acc, x| acc.wrapping_add(*x))]);
    content_params.map(|_| ()).map_err(|ce| Plus3DosError::Content(ce))
}

fn plus3dos_read(filename: &str) -> Result<(Vec<u8>, Plus3DosFile), Plus3DosError> {
    read_file(filename, plus3dos_parse_file).map_err(|fe| Plus3DosError::File(fe))
}

fn plus3dos_save(filename: &str, p3dos: &Plus3DosFile) -> Result<(), Plus3DosError> {
    let mut buf = AnnotatedBuf::new();
    plus3dos_unparse_file(&mut buf, p3dos)?;
    write_file(filename, &buf.bytes).map_err(|fe| Plus3DosError::File(fe))
}

fn parse_content_header(i: &[u8], ctag: u8) -> nom::IResult<&[u8], ContentHeader> {
    let (i, data_length) = le_u16(i)?;
    let (i, content_params) = match ctag {
        0x00 => cut(map(
            tuple((
                map(le_u16, |w| if w >= 0x8000 { None } else { Some(w) }),
                le_u16,
            )),
            |(autostart, vars_offset)| ContentParams::Program{autostart, vars_offset}
        ))(i)?,
        0x01 | 0x02 => cut(map(
            tuple((
                le_u8,
                |i| parse_basic_varhead(if ctag == 0x01 {0b100} else {0b110}, i),
                le_u16
            )),
            |(_, name, _)| if ctag == 0x01 { ContentParams::NumberArray{name} } else { ContentParams::CharacterArray{name} }
        ))(i)?,
        0x03 => cut(alt((
            map(
                tuple((
                    verify(le_u16, |load_addr| *load_addr == 16384 && data_length == 6912),
                    le_u16,//tag([0x00, 0x80]),
                )),
                |(_, unused)| ContentParams::Screen{unused}
            ),
            map(
                tuple((
                    le_u16,
                    le_u16,//tag([0x00, 0x80]),
                )),
                |(load_addr, unused)| ContentParams::Code{load_addr, unused}
            ),
        )))(i)?,
        _ => panic!("ctag={}, data_length={}", ctag, data_length),
    };
    Ok( (i, ContentHeader{data_length, content_params}) )
}

fn tap_parse_content_header(i: &[u8]) -> nom::IResult<&[u8], ([u8; 10], ContentHeader)> {
    let (i, ctag) = verify(le_u8, |x| *x < 4)(i)?;
    let (i, name) = nom::bytes::complete::take(10usize)(i)?;
    let (i, ch) = parse_content_header(i, ctag)?;

    Ok( (i, (name.try_into().unwrap(), ch)) )
}

fn unparse_content_header<A: Default + From<BasicTag>>(o: &mut AnnotatedBuf<A>, header: &ContentHeader) -> Result<(), ContentError> {
    let dl = header.data_length.to_le_bytes();
    o.reset(BasicTag::DataLength);
    o.push(dl[0]);
    o.push(dl[1]);
    o.reset(BasicTag::Unknown);

    match header.content_params {
        ContentParams::Program{autostart, vars_offset} => {
            let ll = autostart.unwrap_or(0x8000).to_le_bytes();
            o.push(ll[0]);
            o.push(ll[1]);
            let vo = vars_offset.to_le_bytes();
            o.push(vo[0]);
            o.push(vo[1]);
        },
        ContentParams::NumberArray{name} => {
            o.push(0xFF); // not used
            unparse_basic_varhead(o, 0b100, name)?;
            o.push(0xFF); // not used
            o.push(0xFF); // not used
        },
        ContentParams::CharacterArray{name} => {
            o.push(0xFF); // not used
            unparse_basic_varhead(o, 0b110, name)?;
            o.push(0xFF); // not used
            o.push(0xFF); // not used
        },
        ContentParams::Code{load_addr, unused} => {
            let la = load_addr.to_le_bytes();
            o.push(la[0]);
            o.push(la[1]);
            o.extend_from_slice(&unused.to_le_bytes()); // TODO:
        },
        ContentParams::Screen{unused} => {
            let la = 16384u16.to_le_bytes();
            o.push(la[0]);
            o.push(la[1]);
            o.extend_from_slice(&unused.to_le_bytes()); // TODO:
        },
    }
    Ok(())
}

fn tap_unparse_content_header(o: &mut AnnotatedBuf<TapTag>, filename: &[u8; 10], header: &ContentHeader) -> Result<(), ContentError> {

    o.push(header.ctag());
    o.extend_from_slice(filename);
    unparse_content_header(o, header);

    Ok(())
}

fn tap_save(filename: &str, tap: &TapFile) -> Result<(), String> {
    let mut buf = AnnotatedBuf::new();
    tap_unparse_file(&mut buf, tap).map_err(|e| format!("{:?}", e))?;
    write_file(filename, &buf.bytes)
}

fn tap_read(filename: &str) -> Result<(Vec<u8>, TapFile), TapError> {
    read_file(filename, tap_parse_file).map_err(|fe| TapError::File(fe))
}

fn tap_parse_block_pair(i0: &[u8]) -> nom::IResult<&[u8], TapBlockPair> {
    let (i1, (filename, content_header)) = map_parser(
        parse_block_body,
        map(
            preceded(
                tag([0x00]),
                verify(tap_parse_content_header, |(f, _)| f.iter().all(|x| *x >= 0x20 && *x < 0x80)),
            ),
            |(f, ch)| (std::str::from_utf8(&f).unwrap().to_owned(), ch)
        )
    )(i0)?;

    let (i2, content) = map_parser(
        parse_block_body,
        preceded(
            tag([0xFF]),
            map_parser(
                nom::bytes::complete::take(content_header.data_length),
                move |i| parse_content(&content_header.content_params, i)
            )
        )
    )(i1)?;

    let (i3, extrablocks) = nom::multi::many0(
        map_parser(
            parse_block_body,
            alt((
                map(preceded(tag([0xFF]), nom::combinator::rest), |bs: &[u8]| ExtraBlock(0xFF, Bytes(bs.to_vec()))),
                // possible 0x00+<unsupported tag> blocks, see 'Bathyscyph'
                map(
                    preceded(tag([0x00]), tuple((verify(le_u8, |b| *b > 3), nom::combinator::rest))),
                    |(ctag, bs)| ExtraBlock(0x00, Bytes({let mut v = vec![ctag]; v.extend_from_slice(bs); v}))
                ),
                // possible 0xA6+.... block, see 'Pac-Man'
                map(preceded(tag([0xA6]), nom::combinator::rest), |bs: &[u8]| ExtraBlock(0xA6, Bytes(bs.to_vec()))),
            ))
        )
    )(i2)?;

    let derived_total_length = i0.len() - i3.len();
    Ok((i3, TapBlockPair{filename: filename.clone(), content, extrablocks, derived_total_length}))
}

fn tap_unparse_block_pair(o: &mut AnnotatedBuf<TapTag>, tap: &TapBlockPair) -> Result<(), TapError> {
    let mut content_block = AnnotatedBuf::new();
    content_block.reset(TapTag::BlockStart);
    content_block.push(0xFF);
    content_block.reset(TapTag::Unknown);
    let content_params = unparse_content(&mut content_block, &tap.content).map_err(|ce| TapError::Content(ce))?;
    if content_block.len() - 1 > 0xFFFF {
        return Err(TapError::ContentBlockLength);
    }
    let content_header = ContentHeader{data_length: (content_block.len() - 1) as u16, content_params};

    let mut header_block = AnnotatedBuf::new();
    header_block.reset(TapTag::BlockStart);
    header_block.push(0x00);
    header_block.reset(TapTag::Unknown);
    let filename: [u8; 10] = tap.filename.as_bytes().try_into().map_err(|_| TapError::InvalidFilename)?;
    tap_unparse_content_header(&mut header_block, &filename, &content_header).map_err(|ce| TapError::Content(ce))?;
    
    tap_unparse_block_body(o, header_block)?;
    tap_unparse_block_body(o, content_block)?;

    for eb in &tap.extrablocks {
        let mut extra_block = AnnotatedBuf::new();
        match eb {
            ExtraBlock(0xFF, Bytes(v)) => {
                extra_block.reset(TapTag::BlockStart);
                extra_block.push(0xFF);
                extra_block.reset(TapTag::Unknown);
                extra_block.extend_from_slice(&v)
            },
            ExtraBlock(0x00, Bytes(v)) if v.len() > 0 && v[0] > 3 => {
                extra_block.reset(TapTag::BlockStart);
                extra_block.push(0x00);
                extra_block.reset(TapTag::Unknown);
                extra_block.extend_from_slice(&v)
            },
            // Pac-Man
            ExtraBlock(0xA6, Bytes(v)) => {
                extra_block.reset(TapTag::BlockStart);
                extra_block.push(0xA6);
                extra_block.reset(TapTag::Unknown);
                extra_block.extend_from_slice(&v)
            },
            _ => return Err(TapError::InvalidExtraBlock),
        }
        tap_unparse_block_body(o, extra_block)?;
    }
    Ok(())
}

fn xor_check(x: &[u8]) -> u8 {
    x.iter().fold(0u8, |acc, x| acc ^ x)
}

fn parse_block_body(i0: &[u8]) -> nom::IResult<&[u8], &[u8]> {
    let (i1, block) = nom::multi::length_data(
        map(
            verify(le_u16, |sz| *sz > 1),
            |total| total - 1
        )
    )(i0)?;

    let (i2, _check) = cut(verify(
        le_u8,
        |c| *c == xor_check(block)
    ))(i1)?;

    Ok((i2, block))
}

fn tap_unparse_block_body(o: &mut AnnotatedBuf<TapTag>, body: AnnotatedBuf<TapTag>) -> Result<(), TapError> {
    if body.len() >= 0xFFFF {
        return Err(TapError::BlockBodyLength)
    }
    let check = xor_check(&body.bytes);
    let sz = body.len() + 1;
    let le = sz.to_le_bytes();
    o.reset(TapTag::BlockBodyLength);
    o.push(le[0]);
    o.push(le[1]);
    o.reset(TapTag::Unknown);
    o.append(body);
    o.reset(TapTag::Checksum);
    o.push(check);
    o.reset(TapTag::Unknown);
    Ok(())
}

fn tap_parse_file(i: &[u8]) -> nom::IResult<&[u8], TapFile> {
    map(
        nom::multi::many0(tap_parse_block_pair),
        |pairs| TapFile {pairs}
    )(i)
}

#[derive(Debug)]
enum ContentError {
    ProgramLength,
    ScreenSize,
    ArrayDimensions,
    LineLength,
    StringLength,
    InvalidVar,
    InvalidKeyword,
    InvalidChar,
    InvalidUdg,
    TooBig(&'static str),
    Todo(&'static str),
}

#[derive(Debug)]
enum TapError {
    Content(ContentError),
    File(String),
    InvalidExtraBlock,
    InvalidFilename,
    BlockBodyLength,
    ContentBlockLength,
    OutputMismatch(usize, usize, usize),
}

#[derive(Debug)]
enum Plus3DosError {
    Content(ContentError),
    File(String),
    OutputMismatch(usize, usize, usize),
}

fn tap_unparse_file(o: &mut AnnotatedBuf<TapTag>, tap: &TapFile) -> Result<(), TapError> {
    for p in &tap.pairs {
        let () = tap_unparse_block_pair(o, p)?;
    }
    Ok( () )
}

struct BasicLine {
    line_number: u16,
    malformed: Option<u16>,
    tokens: Vec<BasicToken>,
}

impl std::fmt::Debug for BasicLine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{} ",
            self.line_number,
            self.malformed.map(|_| '*').unwrap_or(' '),
        )?;
        let mut co = ColoredWrite {
            write: f,
            n: 0,
        };
        for (n, x) in self.tokens.iter().enumerate() {
            colorfmt_basic_token(&mut co, x)?;
        }
        write!(f, "{}{}", Fg(Reset), Bg(Reset))
    }
}

const KEYWORDS: &[&'static str] = &[
    "RND", "INKEY$", "PI", "FN", "POINT", "SCREEN$", "ATTR", "AT", "TAB", "VAL$", "CODE",
    "VAL", "LEN", "SIN", "COS", "TAN", "ASN", "ACS", "ATN", "LN", "EXP", "INT", "SQR", "SGN", "ABS", "PEEK", "IN",
    "USR", "STR$", "CHR$", "NOT", "BIN", "OR", "AND", "<=", ">=", "<>", "LINE", "THEN", "TO", "STEP", "DEFFN", "CAT",
    "FORMAT", "MOVE", "ERASE", "OPEN#", "CLOSE#", "MERGE", "VERIFY", "BEEP", "CIRCLE", "INK", "PAPER", "FLASH", "BRIGHT", "INVERSE", "OVER", "OUT",
    "LPRINT", "LLIST", "STOP", "READ", "DATA", "RESTORE", "NEW", "BORDER", "CONTINUE", "DIM", "REM", "FOR", "GOTO", "GOSUB", "INPUT", "LOAD",
    "LIST", "LET", "PAUSE", "NEXT", "POKE", "PRINT", "PLOT", "RUN", "SAVE", "RANDOMIZE", "IF", "CLS", "DRAW", "CLEAR", "RETURN", "COPY"
];

#[derive(Debug)]
enum BasicToken {
    Arrow,
    Pound,
    Ascii(char),
    Copyright,
    UdgBlock(u8),
    UdgLetter(char),
    Keyword(&'static str),
    Number(BasicNumber),
    Return,
    Ink(u8),
    Paper(u8),
    Flash(u8),
    Bright(u8),
    Inverse(u8),
    Over(u8),
    At(u8, u8),
    Tab(u8),
    // TODO: comma?
    Other(u8),
}

struct ColoredWrite<'f, 'a> {
    write: &'f mut std::fmt::Formatter<'a>,
    n: usize,
}

use termion::color::*;

impl ColoredWrite<'_, '_> {
    fn reset_fg(&mut self) -> std::fmt::Result {
        self.write.write_str(Reset.fg_str())
    }
    fn reset_bg(&mut self) -> std::fmt::Result {
        self.write.write_str(Reset.bg_str())
    }
    fn set_fg(&mut self, c: &dyn termion::color::Color) -> std::fmt::Result {
        c.write_fg(&mut self.write)
    }
    fn set_bg(&mut self, c: &dyn termion::color::Color) -> std::fmt::Result {
        c.write_bg(&mut self.write)
    }
    fn interleave_bg(&mut self, c: &dyn termion::color::Color) -> std::fmt::Result {
        self.n += 1;
        if self.n % 2 == 0 {
            self.reset_bg()
        } else {
            self.set_bg(c)
        }
    }
}

impl std::fmt::Write for ColoredWrite<'_, '_> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.write.write_str(s)
    }
}

fn colorfmt_basic_token(co: &mut ColoredWrite, token: &BasicToken) -> std::fmt::Result {
    use BasicToken::*;
    match token {
        Arrow =>        { co.reset_bg()?; co.set_fg(&Magenta)?; co.write_char('^')                         },
        Pound =>        { co.reset_bg()?; co.set_fg(&Magenta)?; co.write_char('$')                         },
        Ascii(c) =>     { co.reset_bg()?; co.reset_fg()?; co.write_char(*c)                                },
        Copyright =>    { co.reset_bg()?; co.set_fg(&Magenta)?; co.write_char('c')                         },
        UdgLetter(c) => { co.set_fg(&Yellow)?;      co.interleave_bg(&Black)?; co.write_char(*c)           },
        Number(n) =>    { co.set_fg(&Blue)?;        co.reset_bg()?; write!(co, "{:?}", n)                  },
        UdgBlock(b) =>  { co.set_fg(&LightYellow)?; co.interleave_bg(&Black)?; write!(co, "{:04b}", b)     },
        Keyword(s) =>   { co.set_fg(&LightGreen)?;  co.interleave_bg(&Black)?; co.write_str(s)             },
        Return =>       { co.set_fg(&LightRed)?;    co.interleave_bg(&Black)?; co.write_str("RET")         },
        Ink(b) =>       { co.set_fg(&LightRed)?;    co.interleave_bg(&Black)?; write!(co, "INK{}", b)      },
        Paper(b) =>     { co.set_fg(&LightRed)?;    co.interleave_bg(&Black)?; write!(co, "PAPER{}", b)    },
        Flash(b) =>     { co.set_fg(&LightRed)?;    co.interleave_bg(&Black)?; write!(co, "FLASH{}", b)    },
        Bright(b) =>    { co.set_fg(&LightRed)?;    co.interleave_bg(&Black)?; write!(co, "BRIGHT{}", b)   },
        Inverse(b) =>   { co.set_fg(&LightRed)?;    co.interleave_bg(&Black)?; write!(co, "INVERSE{}", b)  },
        Over(b) =>      { co.set_fg(&LightRed)?;    co.interleave_bg(&Black)?; write!(co, "OVER{}", b)     },
        At(y, x) =>     { co.set_fg(&LightRed)?;    co.interleave_bg(&Black)?; write!(co, "AT{},{}", y, x) },
        Tab(b) =>       { co.set_fg(&LightRed)?;    co.interleave_bg(&Black)?; write!(co, "TAB{}", b)      },
        Other(b) =>     { co.set_fg(&LightBlue)?;   co.interleave_bg(&Black)?; write!(co, "{:02X}", b)     },
    }
}

fn parse_basic_token(i: &[u8]) -> nom::IResult<&[u8], BasicToken> {
    alt((
        map(tag([0x5E]), |_| BasicToken::Arrow),
        map(tag([0x60]), |_| BasicToken::Pound),
        map(tag([0x7F]), |_| BasicToken::Copyright),
        map(verify(le_u8, |x| *x >= 0x20 && *x < 0x7F), |x| BasicToken::Ascii(x as char)),
        map(verify(le_u8, |x| *x >= 0x80 && *x < 0x90), |x| BasicToken::UdgBlock(x - 0x80)),
        map(verify(le_u8, |x| *x >= 0x90 && *x < 0xA5), |x| BasicToken::UdgLetter((b'A' + (x - 0x90)) as char)),
        map(verify(le_u8, |x| *x >= 0xA5), |x| BasicToken::Keyword(KEYWORDS[(x - 0xA5) as usize])),
        map(preceded(tag([0x0E]), parse_basic_number), BasicToken::Number),
        map(tag([0x0D]), |_| BasicToken::Return),
        map(preceded(tag([0x10]), le_u8), |x| BasicToken::Ink(x)),
        map(preceded(tag([0x11]), le_u8), |x| BasicToken::Paper(x)),
        map(preceded(tag([0x12]), le_u8), |x| BasicToken::Flash(x)),
        map(preceded(tag([0x13]), le_u8), |x| BasicToken::Bright(x)),
        map(preceded(tag([0x14]), le_u8), |x| BasicToken::Inverse(x)),
        map(preceded(tag([0x15]), le_u8), |x| BasicToken::Over(x)),
        map(preceded(tag([0x16]), tuple((le_u8, le_u8))), |(y, x)| BasicToken::At(y, x)),
        map(preceded(tag([0x17]), le_u8), |x| BasicToken::Tab(x)),
        map(le_u8, BasicToken::Other),
    ))(i)
}

fn unparse_basic_token<A: Default + From<BasicTag>>(o: &mut AnnotatedBuf<A>, token: &BasicToken) -> Result<(), ContentError> {
    match token {
        BasicToken::Arrow => o.push(0x5E),
        BasicToken::Pound => o.push(0x60),
        BasicToken::Copyright => o.push(0x7F),
        BasicToken::Ascii(x) => {
            // TODO: arrow/pound
            if *x >= ' ' && *x <= '~' { o.push(*x as u8) } else { return Err(ContentError::InvalidChar) }
        },

        BasicToken::UdgBlock(x) => {
            if *x < 0x10 { o.push(*x + 0x80) } else { return Err(ContentError::InvalidUdg) }
        },
        BasicToken::UdgLetter(c) => {
            if *c >= 'A' && *c <= 'U' { o.push(*c as u8 - b'A' + 0x90) } else { return Err(ContentError::InvalidUdg) }
        },
        BasicToken::Keyword(kw) => {
            // TODO: better lookup
            KEYWORDS.iter().enumerate()
                .find(|(_, x)| *x == kw)
                .map(|(i, _)| {
                    o.reset(BasicTag::Keyword);
                    o.push(i as u8 + 0xA5);
                    o.reset(BasicTag::Unknown);
                })
                .ok_or(ContentError::InvalidKeyword)?
        },
        BasicToken::Number(n) => { o.push(0x0E); unparse_basic_number(o, n)? },
        BasicToken::Return => o.push(0x0D),
        BasicToken::Ink(x) => { o.push(0x10); o.push(*x) },
        BasicToken::Paper(x) => { o.push(0x11); o.push(*x) },
        BasicToken::Flash(x) => { o.push(0x12); o.push(*x) },
        BasicToken::Bright(x) => { o.push(0x13); o.push(*x) },
        BasicToken::Inverse(x) => { o.push(0x14); o.push(*x) },
        BasicToken::Over(x) => { o.push(0x15); o.push(*x) },
        BasicToken::At(y, x) => { o.push(0x16); o.push(*y); o.push(*x) },
        BasicToken::Tab(x) => { o.push(0x17); o.push(*x) },
        BasicToken::Other(x) => o.push(*x),
    };
    Ok(())
}

// isolated lines, i0 is *all* lines up to vars
fn parse_basic_line(i0: &[u8]) -> nom::IResult<&[u8], BasicLine> {
    let (i, line_number) = nom::number::complete::be_u16(i0)?;
    map(
        alt((
            map(
                nom::combinator::complete(tuple((
                    map_parser(
                        nom::multi::length_data(
                            map(
                                verify(le_u16, |sz| *sz >= 1),
                                |total| total - 1
                            )
                        ),
                        nom::combinator::all_consuming(nom::multi::many0(parse_basic_token))
                    ),
                    tag([0x0D])
                ))),
                |(tokens, _)| (None, tokens)
            ),

            // Parse malformed (which is actually ok in some cases, (see Ninjajar)
            // TODO: what if token (e.g number happens to be incomplete)
            tuple((map(le_u16, Some), nom::combinator::all_consuming(nom::multi::many0(parse_basic_token)))),
        )),
        move |(malformed, tokens)| BasicLine{line_number, malformed, tokens}
    )(i)
}

fn unparse_basic_line<A: Default + From<BasicTag>>(o: &mut AnnotatedBuf<A>, line: &BasicLine) -> Result<(), ContentError> {
    o.reset(BasicTag::LineNumber);
    o.extend_from_slice(&line.line_number.to_be_bytes());
    o.reset(BasicTag::Unknown);
    match line.malformed {
        Some(fake_len) => {
            o.extend_from_slice(&fake_len.to_le_bytes());
            for t in &line.tokens {
                unparse_basic_token(o, &t)?;
            }
        },
        None => {
            let len_offset = o.len();
            o.push(0xFF); // length placeholder
            o.push(0xFF);
            let offset0 = o.len();
            for t in &line.tokens {
                unparse_basic_token(o, &t)?;
            }
            o.push(0x0D);
            let len: u16 = (o.len() - offset0).try_into().map_err(|_| ContentError::LineLength)?;
            o.bytes[len_offset + 0] = len.to_le_bytes()[0];
            o.bytes[len_offset + 1] = len.to_le_bytes()[1];
        },
    }
    Ok(())
}

struct BasicNumber {
    exponent: u8,
    mantissa: (u8, u8, u8, u8),
}

impl std::fmt::Debug for BasicNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}_{},{},{},{}", self.exponent, self.mantissa.0, self.mantissa.1, self.mantissa.2, self.mantissa.3)
    }
}

#[derive(Debug)]
enum BasicVar {
    Number{name: String, value: BasicNumber},
    NumberArray{letter: char, dims: Vec<u16>, values: Vec<BasicNumber>},
    LoopIndex{letter: char, value: BasicNumber, limit: BasicNumber, step: BasicNumber, line: u16, stmt: u8},
    String{letter: char, text: Bytes},
    CharArray{letter: char, dims: Vec<u16>, values: Vec<u8>},
}

fn parse_basic_number(i: &[u8]) -> nom::IResult<&[u8], BasicNumber> {
    map(
        tuple((le_u8, tuple((le_u8, le_u8, le_u8, le_u8)))),
        |(exponent, mantissa)| BasicNumber{exponent, mantissa}
    )(i)
}

fn unparse_basic_number<A: Default + From<BasicTag>>(o: &mut AnnotatedBuf<A>, n: &BasicNumber) -> Result<(), ContentError> {
    o.reset(BasicTag::Number);
    o.push(n.exponent);
    o.push(n.mantissa.0);
    o.push(n.mantissa.1);
    o.push(n.mantissa.2);
    o.push(n.mantissa.3);
    o.reset(BasicTag::Unknown);
    Ok(())
}

fn parse_basic_varhead(mask: u8, i: &[u8]) -> nom::IResult<&[u8], char> {
    verify(map(
        verify(le_u8, |x| (*x >> 5) == mask),
        |b| ((b & 0b000_11111) + 0x60) as char
    ), |c| *c >= 'a' && *c <= 'z')(i)
}

fn unparse_basic_varhead<A: Default + From<BasicTag>>(o: &mut AnnotatedBuf<A>, mask: u8, letter: char) -> Result<(), ContentError> {
    if letter >= 'a' && letter <= 'z' {
        o.reset(BasicTag::VarHead);
        o.push((mask << 5) | letter as u8 - 0x60);
        o.reset(BasicTag::Unknown);
        Ok(())
    } else {
        Err(ContentError::InvalidVar)
    }
}

fn isalphanum(c: char) -> bool {
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
}

fn parse_basic_vartail(i: &[u8]) -> nom::IResult<&[u8], Vec<char>> {
    map(
        nom::multi::many_till(
            verify(map(verify(le_u8, |x| (*x >> 7) == 0), |b| b as char), |c| isalphanum(*c)),
            verify(map(verify(le_u8, |x| (*x >> 7) == 1), |x| (x & 0b0_1111111) as char), |c| isalphanum(*c)),
        ),
        |(mut vec, last)| { vec.push(last); vec }
    )(i)
}

fn unparse_basic_vartail<A: Default + From<BasicTag>>(o: &mut AnnotatedBuf<A>, tail: &[char]) -> Result<(), ContentError> {
    o.reset(BasicTag::VarTail);
    for (i, c) in tail.iter().enumerate() {
        if isalphanum(*c) {
            let lastbit = if i + 1 == tail.len() { 0b1_0000000 } else { 0b0_0000000 };
            o.push(*c as u8 | lastbit);
        } else {
            return Err(ContentError::InvalidVar)
        }
    }
    o.reset(BasicTag::Unknown);
    Ok(())
}

fn parse_basic_array<'a, T, F>(parser: F, i: &'a[u8]) -> nom::IResult<&'a[u8], (Vec<u16>, Vec<T>)>
where F: Fn(&'a[u8]) -> nom::IResult<&'a[u8], T>, T: std::fmt::Debug {
    let (i, ndims) = le_u8(i)?;
    let (i, dims) = nom::multi::count(le_u16, ndims as usize)(i)?;
    let nvalues = dims.iter().fold(1, |acc, x| acc * x);
    let (i, values) = nom::multi::count(parser, nvalues as usize)(i)?;

    Ok((i, (dims, values)))
}

fn unparse_basic_array<A: Default, T, F>(o: &mut AnnotatedBuf<A>, unparser: F, dims: &[u16], values: &[T]) -> Result<(), ContentError>
where F: Fn(&mut AnnotatedBuf<A>, &T) -> Result<(), ContentError> {
    if dims.len() > 0xFF { return Err(ContentError::ArrayDimensions) }
    o.push(dims.len() as u8);
    for d in dims {
        o.extend_from_slice(&d.to_le_bytes());
    }
    for v in values {
        unparser(o, v)?;
    }

    Ok(())
}

// From official basic programming manual
fn parse_basic_var(i: &[u8]) -> nom::IResult<&[u8], BasicVar> {
    // TODO: vvvv
    alt((
        map(
            tuple((|i| parse_basic_varhead(0b011, i), parse_basic_number)),
            |(letter, value)| BasicVar::Number {
                name: format!("{}", letter),
                value
            }
        ),
        map(
            tuple((|i| parse_basic_varhead(0b101, i), parse_basic_vartail, parse_basic_number)),
            |(letter, chars, value)| BasicVar::Number {
                name: chars.into_iter().fold(format!("{}", letter), |mut acc, x| {acc.push(x); acc}),
                value
            }
        ),
        map(
            tuple((
                |i| parse_basic_varhead(0b111, i),
                parse_basic_number,
                parse_basic_number,
                parse_basic_number,
                le_u16,
                le_u8,
            )),
            |(letter, value, limit, step, line, stmt)| BasicVar::LoopIndex{
                letter, value, limit, step, line, stmt
            }
        ),
        map(
            tuple((
                |i| parse_basic_varhead(0b110, i),
                le_u16, // TODO:
                |i| parse_basic_array(le_u8, i)
            )),
            |(letter, _, (dims, values))| BasicVar::CharArray{letter, dims, values}
        ),
        map(
            tuple((
                |i| parse_basic_varhead(0b100, i),
                le_u16, // TODO:
                |i| parse_basic_array(parse_basic_number, i)
            )),
            |(letter, _, (dims, values))| BasicVar::NumberArray{letter, dims, values}
        ),
        map(
            tuple((
                |i| parse_basic_varhead(0b010, i),
                nom::multi::length_data(le_u16)
            )),
            |(letter, text)| BasicVar::String{letter, text: Bytes(text.to_vec())}
        ),
    ))(i)
}

fn unparse_basic_var<A: Default + From<BasicTag>>(o: &mut AnnotatedBuf<A>, var: &BasicVar) -> Result<(), ContentError> {
    match var {
        BasicVar::Number{name, value} => {
            match name.chars().count() {
                0 => return Err(ContentError::InvalidVar),
                1 => {
                    unparse_basic_varhead(o, 0b011, name.chars().nth(0).unwrap())?;
                },
                _ => {
                    unparse_basic_varhead(o, 0b101, name.chars().nth(0).unwrap())?;
                    unparse_basic_vartail(o, &name.chars().skip(1).collect::<Vec<_>>())?;
                },
            }
            unparse_basic_number(o, value)
        },
        BasicVar::LoopIndex{letter, value, limit, step, line, stmt} => {
            unparse_basic_varhead(o, 0b111, *letter)?;
            unparse_basic_number(o, value)?;
            unparse_basic_number(o, limit)?;
            unparse_basic_number(o, step)?;
            o.extend_from_slice(&line.to_le_bytes());
            o.push(*stmt);
            Ok(())
        },
        BasicVar::CharArray{letter, dims, values} => {
            unparse_basic_varhead(o, 0b110, *letter)?;
            let length_offset = o.len();
            o.push(0xFF); // placeholder
            o.push(0xFF);
            let array_start = o.len();
            let res = unparse_basic_array(o, |o, x| Ok(o.push(*x)), dims, values);
            let array_length = o.len() - array_start;
            o.bytes[length_offset..length_offset+2].copy_from_slice(&(array_length as u16).to_le_bytes());
            res
        },
        BasicVar::NumberArray{letter, dims, values} => {
            unparse_basic_varhead(o, 0b100, *letter)?;
            let length_offset = o.len();
            o.push(0xFF); // placeholder
            o.push(0xFF);
            let array_start = o.len();
            let res = unparse_basic_array(o, unparse_basic_number::<A>, dims, values);
            let array_length = o.len() - array_start;
            o.bytes[length_offset..length_offset+2].copy_from_slice(&(array_length as u16).to_le_bytes());
            res
        },
        BasicVar::String{letter, text: Bytes(text)} => {
            unparse_basic_varhead(o, 0b010, *letter)?;
            if text.len() > 0xFFFF { return Err(ContentError::StringLength); }
            o.extend_from_slice(&(text.len() as u16).to_le_bytes());
            o.extend_from_slice(text);
            Ok(())
        },
    }
}

// `iso` is basic block, isolated
fn parse_content<'a>(params: &ContentParams, iso: &'a[u8]) -> nom::IResult<&'a[u8], Content> {
    match params {
        ContentParams::Program {autostart, vars_offset} =>
            cut(map(
                tuple((
                    map_parser(
                        nom::bytes::complete::take(*vars_offset),
                        nom::combinator::all_consuming(nom::multi::many0(parse_basic_line))
                    ),
                    alt((
                        nom::combinator::all_consuming(map(
                            nom::multi::many0(parse_basic_var), VarsBlock::Ok
                        )),
                        nom::combinator::all_consuming(map(
                            nom::combinator::rest, |bs: &[u8]| VarsBlock::Junk(Bytes(bs.to_vec()))
                        )),
                    ))
                )),
                |(lines, vars)| Content::Program {autostart: *autostart, lines, vars}
            ))(iso),
        ContentParams::Screen {unused} =>
            Ok((
                &[],
                Content::Screen{bitmap: Bytes(iso[0..256*192/8].to_vec()), attribs: Bytes(iso[256*192/8..].to_vec()), unused: *unused}
            )),
        ContentParams::Code {load_addr, unused} =>
            Ok((
                &[],
                Content::Code{addr: *load_addr, data: Bytes(iso.to_vec()), unused: *unused}
            )),
        ContentParams::NumberArray {name} => cut(nom::combinator::all_consuming(map(
            |i| parse_basic_array(parse_basic_number, i),
            |(dims, values)| Content::NumberArray{name: *name, dims, values}
        )))(iso),
        ContentParams::CharacterArray {name} => cut(nom::combinator::all_consuming(map(
            |i| parse_basic_array(le_u8, i),
            |(dims, values)| Content::CharacterArray{name: *name, dims, values}
        )))(iso),
    }
}

fn unparse_content<A: Default + From<BasicTag>>(o: &mut AnnotatedBuf<A>, content: &Content) -> Result<ContentParams, ContentError> {
    match content {
        Content::Program{autostart, lines, vars} => {
            let offset0 = o.len();
            for l in lines {
                unparse_basic_line(o, l)?;
            }
            let vars_offset = (o.len() - offset0).try_into().map_err(|_| ContentError::ProgramLength)?;
            match vars {
                VarsBlock::Ok(vs) => for v in vs { unparse_basic_var(o, v)?; },
                VarsBlock::Junk(Bytes(bs)) => o.extend_from_slice(&bs),
            }
            Ok(ContentParams::Program{autostart: *autostart, vars_offset})
        },
        Content::Screen{bitmap: Bytes(xs), attribs: Bytes(ys), unused} => {
            if xs.len() != 256*192/8 || ys.len() != 768 {
                return Err(ContentError::ScreenSize);
            }
            o.extend_from_slice(xs);
            o.extend_from_slice(ys);
            Ok(ContentParams::Screen{unused: *unused})
        },
        Content::Code{addr, data: Bytes(xs), unused} => {
            o.extend_from_slice(xs);
            Ok(ContentParams::Code {load_addr: *addr, unused: *unused})
        },
        Content::NumberArray{name, dims, values} =>
            unparse_basic_array(o, unparse_basic_number::<A>, dims, values).map(|()| {
                ContentParams::NumberArray {name: *name}
            }),
        Content::CharacterArray{name, dims, values} =>
            unparse_basic_array(o, |o, x| Ok(o.push(*x)), dims, values).map(|()| {
                ContentParams::CharacterArray {name: *name}
            }),
    }
}

fn main() {
    let cmd = std::env::args().nth(1);
    let file = std::env::args().nth(2);
    match (cmd.as_ref().map(|s| s.as_str()), file) {
        (Some("asm"), None) => {
            let mut buffer = String::new();
            std::io::stdin().read_to_string(&mut buffer).unwrap();
            buffer.push_str("\n"); // make sure last line is complete
            match parse(&buffer) {
                Ok(("", ds)) => {
                    println!("---- INPUT --------------------");
                    for d in &ds {
                        println!("{:?}", d);
                    }
                    println!("---- RESOLVE --------------------");
                    match resolve(&ds) {
                        Ok((org, is, lookup)) => {
                            let vec = print_listing(org, &is, &lookup);
                            println!("---- CONSTANTS -----------------");
                            for b in lookup.byte_consts {
                                println!("${} = {} #{:02X} %{:08b}", b.0, b.1, b.1, b.1);
                            }
                            for w in lookup.word_consts {
                                println!("$${} = {} #{:04X}", w.0, w.1, w.1);
                            }
                            println!("---- LABELS --------------------");
                            println!("org = {}", org);
                            for l in lookup.labels {
                                println!("@{} = {}", l.0, l.1);
                            }
                            println!("--> raz.bin");
                            save_bin("raz.bin", &vec);
                        },
                        Err(e) => println!("{:?}", e),
                    }
                },
                other => println!("{:?}", other),
            }
        },
        (Some("+3dos"), Some(f)) => {
            let res = plus3dos_read(&f).and_then(|(ori_bytes, p3dos)| {
                println!("---------- +3DOS: {} ----------\n{:#?}", f, p3dos);
                let mut buf = AnnotatedBuf::new();
                let res = plus3dos_unparse_file(&mut buf, &p3dos);
                let (mismatches, s) = print_annotated_split(&ori_bytes, &buf);
                println!("{}", s);
                res.and_then(|res|
                    if mismatches == 0 && ori_bytes.len() == buf.len() {
                        Ok(())
                    } else {
                        Err(Plus3DosError::OutputMismatch(mismatches, ori_bytes.len(), buf.len()))
                    }
                )
            });
            println!("{}: {:?}", f, res);
        },
        (Some("list-tap"), Some(f)) => {
            let res = tap_read(&f).map(|(ori_bytes, tap)| {
                println!("---------- TAP: {} ----------\n{:#?}", f, tap);
                let mut cur_offset = 0;
                for t in tap.pairs {
                    println!("entry: `{}`, start: {}, length: {}", t.filename, cur_offset, t.derived_total_length);
                    cur_offset += t.derived_total_length;
                }
                println!("file_length: {}, calculated: {}", ori_bytes.len(), cur_offset);
            });
            println!("{}: {:?}", f, res);
        },
        (Some("tap"), Some(f)) => {

            let res = tap_read(&f).and_then(|(ori_bytes, tap)| {
                println!("---------- TAP: {} ----------\n{:#?}", f, tap);
                let mut buf = AnnotatedBuf::new();
                let res = tap_unparse_file(&mut buf, &tap);
                let (mismatches, s) = print_annotated_split(&ori_bytes, &buf);
                println!("{}", s);
                res.and_then(|res|
                    if mismatches == 0 && ori_bytes.len() == buf.len() {
                        Ok(())
                    } else {
                        Err(TapError::OutputMismatch(mismatches, ori_bytes.len(), buf.len()))
                    }
                )
            });
            println!("{}: {:?}", f, res);
        },
        (Some("bad-tap"), Some(f)) => {
            let tap = TapFile {
                pairs: vec![
                    TapBlockPair {
                        filename: "bla       ".to_owned(),
                        content: Content::Program {
                            autostart: None,
                            lines: vec![
                                BasicLine{
                                    line_number: 2357,
                                    malformed: None,
                                    tokens: vec![
                                        BasicToken::Keyword("REM"),
                                        BasicToken::Number(BasicNumber{exponent: 0, mantissa: (0, 0, 0, 0)}),
                                        BasicToken::At(23, 57),
                                        //BasicToken::Other(0x0E), // start number
                                    ]
                                },
                            ],
                            vars: VarsBlock::Ok(vec![]),
                        },
                        extrablocks: vec![],
                        derived_total_length: 0,
                    }
                ]
            };
            let res = tap_save(&f, &tap);
            println!("{}: {:?}", f, res);
        },
        _ => {
            println!("invalid arguments");
            println!("`raz asm` -- assemble from stdin");
            println!("`raz +3dos <file>` -- parse +3DOS file");
            println!("`raz list-tap <file>` -- list blocks of TAP file");
            println!("`raz tap <file>` -- parse TAP file");
        },
    }
}
