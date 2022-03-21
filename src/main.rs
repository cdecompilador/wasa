use std::collections::HashMap;
use std::cell::RefCell;
use std::rc::Rc;
use std::cell::Cell;
use std::borrow::Borrow;

/// All the errors the execution of an instruction can produce in the Vm
#[derive(Debug)]
pub enum Error {
    /// Some instruction required a number of operands avaible on the stack
    /// and its retireval would cause and underflow.
    StackUnderflow(usize),

    /// The instruction opcode is not recognized by the Vm.
    IllegalInstruction(usize),

    /// The operand that comes with the instruction is invalid on his context.
    IllegalOperand(Inst),

    /// Tried to divide a number by zero (integer or decimal).
    ZeroDivision(usize),

    /// An arithmetic operation caused overflow (positive or negative)
    ArithOverflow(usize),

    /// Tried to move the instruction pointer to an invalid address.
    InvalidAddr(usize),

    /// Function not found on the loaded module.
    FuncNotFound(usize, String),
}

/// All the operations that the Vm supports with each of his operands.
#[derive(Debug, Clone, Copy)]
pub enum Inst {
    /// Stack manipulation operations
    ConstI32(i32), // Push
    // Dup,

    /// Memory manipulation
    // LocalGet,
    // LocalTee,
    // LocalSet,
    // GlobalGet,
    // GlobalSet,

    /// Arithmetic-logic operations.
    PlusI32,
    // Minus,
    // Mult,
    // Div,

    /// Unary operations
    // ...

    /// Conversions
    // Extend,
    // Wrap,
    // Trunc
    // Demote,
    // Promote,
    // Convert
    // Reinterpret,

    /// Binary comparison operations
    // Eq,

    /// Control flow operations
    // Jmp,
    // JmpIf,

    /// Virtual machine state manipulation
    Halt,
}

/// Numeric types
pub enum NumType {
    Int32,
    Int64,
    UInt32,
    UInt64,

    /// Following IEEE 754
    Float32, 
    Float64
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    NumType,
}

#[derive(Debug, Clone, Default)]
pub struct FuncType {
    input: Vec<Type>, 
    output: Vec<Type> 
}

/// A wasm function.
#[derive(Debug, Clone)]
pub struct Func {
    /// What parameters accepts and what returns, is needed to know the size
    /// of its local frame.
    signature: FuncType,

    /// This is mutable on the function call, points to the idx on the Vm where
    /// its local frame starts.
    locals_start: Cell<usize>,

    /// The instruction stream.
    body: Box<[Inst]>,
}

impl Func {
    /// Create a new function, its locals_start still needs to be set
    pub fn new(signature: FuncType, body: Box<[Inst]>) -> Self {
        Self {
            signature,
            locals_start: Cell::new(0),
            body,
        }
    }
}

/// Following `https://webassembly.github.io/spec/core/syntax/modules.html`
pub struct Module {
    /// All the declared functions of the module, indexed via their name
    funcs: HashMap<String, Rc<Func>>,

    /// The name of start function (where the execution begins)
    start: String,
}

/// A stack-based virtual machine that in a future will emulate wasm. It's 
/// components are separated in memory, the stack, program and other future
/// regions do not shared address space.
pub struct Vm {
    /// The stack.
    stack: Vec<u32>,

    /// The instruction pointer.
    ///
    /// TODO: Handle returning from functions, maybe moving this to `Func`
    ip: usize,

    /// Flag to know if the Vm has halted (needs exit).
    halt: bool,

    /// The linear memory used by the function to store random access data and
    /// the paremeter
    locals: Vec<u32>,

    /// Current function on execution
    curr_func: Rc<Func>,

    /// The loaded program
    module: Module,
}

impl Vm {
    /// Instantiates a `Vm` with a certain program.
    pub fn load(mut module: Module) -> Result<Self, Error> {
        // Retrieve the start function of the module and set it as the current
        // function on execution (its local frame is already correct, pointing
        // to 0)
        let curr_func = module.funcs.get_mut(&module.start)
            .ok_or(Error::FuncNotFound(0, module.start.clone()))?
            .clone();

        Ok(Self {
            stack: Vec::with_capacity(1024),
            locals: Vec::with_capacity(1024),
            curr_func,
            ip: 0,
            halt: false,
            module 
        })
    }

    /// Execute a single instruction on the Vm, the `func` argument is used to
    /// pass the current function in execution
    ///
    /// # Returns
    /// The new function call to retrieve from the module
    pub fn execute_inst(
        &mut self, 
    ) -> Result<Option<String>, Error> {
        // Bound check the instruction pointer
        if self.ip >= self.curr_func.body.len() {
            return Err(Error::InvalidAddr(self.ip));
        }

        // Fetch the instruction
        let inst = self.curr_func.body[self.ip];

        // Incrase the instruction pointer, consider that when using relative
        // jumps we must substract 1
        self.ip += 1;

        match inst {
            Inst::ConstI32(op) => {
                self.stack.push(op as u32);
            }
            Inst::PlusI32 => {
                let top = self.stack.pop()
                    .ok_or(Error::StackUnderflow(self.ip))?;
                self.stack.last_mut()
                    .and_then(|op| {
                        Some(*op = (*op as i32)
                            .checked_add(top as i32) 
                            .ok_or(Error::ArithOverflow(self.ip)).unwrap()
                            as u32)
                    })
                    .ok_or(Error::StackUnderflow(self.ip))?;
                self.stack.last_mut()
                    .map(|_| 200).unwrap();
            }
            /*
            Inst::Minus => {
                let top = self.stack.pop()
                    .ok_or(Error::StackUnderflow)?;
                self.stack.last_mut()
                    .and_then(|op| {
                        Some(*op = (*op as i32 - top as i32) as u32)
                    })
                    .ok_or(Error::StackUnderflow)?;
            }
            Inst::Mult => {
                let top = self.stack.pop()
                    .ok_or(Error::StackUnderflow)?;
                self.stack.last_mut()
                    .and_then(|op| {
                        Some(op.0 *= top.0)
                    })
                    .ok_or(Error::StackUnderflow)?;
            }
            Inst::Div => {
                let top = self.stack.pop()
                    .ok_or(Error::StackUnderflow)?;
                self.stack.last_mut()
                    .and_then(|op| {
                        if top.0 == 0 { 
                            None Ejercicio de c
                        } else { 
                            Some(op.0 /= top.0) 
                        }
                    })
                    .ok_or(Error::ZeroDivision)?;
            }
            Inst::Eq => {
                let top = self.stack.pop()
                    .ok_or(Error::StackUnderflow)?;
                self.stack.last_mut()
                    .and_then(|op| {
                        if op.0 == top.0 {
                            Some(Word(1))
                        } else {
                            Some(Word(0))
                        }
                    })
                    .ok_or(Error::StackUnderflow)?; 
            }
            Inst::Jmp(addr) => {
                self.ip = addr.0.try_into()
                    .map_err(|_| Error::IllegalOperand(inst))?;
            }
            Inst::JmpIf(addr) => {
                let top = self.stack.last().ok_or(Error::StackUnderflow)?;
                if top.0 == 1 {
                    self.ip = addr.0.try_into()
                        .map_err(|_| Error::IllegalOperand(inst))?;
                }
            }
            */
            Inst::Halt => {
                self.halt = true;
            }
        }

        Ok(None)
    }

    /// Starts the execution of the provided wasm module
    pub fn run(&mut self) -> Result<(), Error> {
        let mut i = 0;
        while !self.halt {
            if i == 30 { break; }
            i += 1;

            if let Some(new_func_name) = self.execute_inst()? {
                self.curr_func = self.module.funcs.get(&new_func_name)
                    .map(|func| {
                        // Setup the func local start reference
                        func.locals_start.set(self.locals.len());
                        func
                    })
                    .ok_or(Error::FuncNotFound(
                            self.ip,
                            self.module.start.clone()))?
                    .clone();
            }
        }

        Ok(())
    }
}

fn main() -> Result<(), Error> {
    let module = Module {
        start: "main".into(),
        funcs: {
            let mut tmp = HashMap::new();
            tmp.insert("main".into(), Rc::new(Func::new(
                    FuncType::default(),
                    Box::new([
                        Inst::ConstI32(1),
                        Inst::ConstI32(1),
                        Inst::PlusI32,
                        Inst::Halt
                    ]))));
            tmp
        }
    };

    let mut vm = Vm::load(module)?;
    vm.run()?;

    dbg!(vm.stack);

    Ok(())
}

