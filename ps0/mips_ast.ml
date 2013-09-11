open Int32

exception CantTranslateError

type label = string

type reg = R0 
     | R1  (* DO NOT USE ME:  assembler temp *)
     | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 
     | R10 | R11 | R12 | R13 | R14 | R15 | R16 | R17 | R18 | R19
     | R20 | R21 | R22 | R23 | R24 | R25 
     | R26 | R27 (* DO NOT USE ME: reserved for OS *)
     | R28
     | R29 | R30 |R31  (* used for special purposes... *)

let reg2str r = 
  match r with
    R0 -> "$0" | R1 -> "$1" | R2 -> "$2" | R3 -> "$3"
  | R4 -> "$4" | R5 -> "$5" | R6 -> "$6" | R7 -> "$7"
  | R8 -> "$8" | R9 -> "$9" | R10 -> "$10" | R11 -> "$11"
  | R12 -> "$12" | R13 -> "$13" | R14 -> "$14" | R15 -> "$15"
  | R16 -> "$16" | R17 -> "$17" | R18 -> "$18" | R19 -> "$19"
  | R20 -> "$20" | R21 -> "$21" | R22 -> "$22" | R23 -> "$23"
  | R24 -> "$24" | R25 -> "$25" | R26 -> "$26" | R27 -> "$27"
  | R28 -> "$28" | R29 -> "$29" | R30 -> "$30" | R31 -> "$31"
  
let str2reg s =
  match s with
    "$0" -> R0 | "$1" -> R1 | "$2" -> R2 | "$3" -> R3 | "$4" -> R4
  | "$5" -> R5 | "$6" -> R6 | "$7" -> R7 | "$8" -> R8 | "$9" -> R9
  | "$10" -> R10 | "$11" -> R11 | "$12" -> R12 | "$13" -> R13
  | "$14" -> R14 | "$15" -> R15 | "$16" -> R16 | "$17" -> R17
  | "$18" -> R18 | "$19" -> R19 | "$20" -> R20 | "$21" -> R21
  | "$22" -> R22 | "$23" -> R23 | "$24" -> R24 | "$25" -> R25
  | "$26" -> R26 | "$27" -> R27 | "$28" -> R28 | "$29" -> R29
  | "$30" -> R30 | "$31" -> R31
  | _ -> R0

let reg2ind r =
  match r with
    R0 -> 0 | R1 -> 1 | R2 -> 2 | R3 -> 3
  | R4 -> 4 | R5 -> 5 | R6 -> 6 | R7 -> 7
  | R8 -> 8 | R9 -> 9 | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15
  | R16 -> 16 | R17 -> 17 | R18 -> 18 | R19 -> 19
  | R20 -> 20 | R21 -> 21 | R22 -> 22 | R23 -> 23
  | R24 -> 24 | R25 -> 25 | R26 -> 26 | R27 -> 27
  | R28 -> 28 | R29 -> 29 | R30 -> 30 | R31 -> 31

(* convert int32 into register *)
let ind2reg i =
  match i with
    0 -> R0 | 1 -> R1 | 2 -> R2 | 3 -> R3
  | 4 -> R4 | 5 -> R5 | 6 -> R6 | 7 -> R7
  | 8 -> R8 | 9 -> R9 | 10 -> R10 | 11 -> R11
  | 12 -> R12 | 13 -> R13 | 14 -> R14 | 15 -> R15
  | 16 -> R16 | 17 -> R17 | 18 -> R18 | 19 -> R19
  | 20 -> R20 | 21 -> R21 | 22 -> R22 | 23 -> R23
  | 24 -> R24 | 25 -> R25 | 26 -> R26 | 27 -> R27
  | 28 -> R28 | 29 -> R29 | 30 -> R30 | 31 -> R31


(* A small subset of the Mips assembly language *)
type inst =
  Add of reg * reg * reg  
| Beq of reg * reg * int32 (* should be int16, but ocaml doesn't have these *) 
| Jr of reg
| Jal of int32 
| Li of reg * int32        
| Lui of reg * int32       (* same here *)
| Ori of reg * reg * int32 (* and here ... *)
| Lw of reg * reg * int32  (* and here ... *)
| Sw of reg * reg * int32  (* and here ... *)

type program = inst list

let zero_top_24_bits (x:int32) : int32 =
  Int32.logand 0x000000FFl x

let zero_top_sixteen_bits (x:int32) : int32 =
  Int32.logand 0x0000FFFFl x

let zero_top_six_bits (x:int32) : int32 =
  Int32.logand 0x03FFFFFFl x

let grab_top_sixteen_bits (x:int32) : int32 =
  shift_right_logical x 16

let inst2bin (i:inst) : int32 =
  match i with
    Add(rd, rs, rt) ->
      (let rd32 = of_int (reg2ind rd) in
       let rs32 = of_int (reg2ind rs) in
       let rt32 = of_int (reg2ind rt) in
       let fields = [of_int 0x20; shift_left rd32 11; shift_left rt32 16; shift_left rs32 21] in
       List.fold_left Int32.logor Int32.zero fields)
  | Beq(rs, rt, offset) ->
    (let rs32 = of_int (reg2ind rs) in
     let rt32 = of_int (reg2ind rt) in
     let offset16 = zero_top_sixteen_bits offset in
     let fields = [offset16; shift_left rt32 16; shift_left rs32 21; shift_left (of_int 4) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Jr(rs) ->
    (let rs32 = of_int (reg2ind rs) in
     let fields = [of_int 8; shift_left rs32 21] in
     List.fold_left Int32.logor Int32.zero fields)
  | Jal(target) ->
    (let target26 = zero_top_six_bits target in
     let fields = [target26; shift_left (of_int 3) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Lui(rt, imm) ->
    (let imm16 = zero_top_sixteen_bits imm in
     let rt32 = of_int (reg2ind rt) in
     let fields = [imm16; shift_left rt32 16; shift_left (of_int 0xf) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Ori(rt, rs, imm) ->
    (let imm16 = zero_top_sixteen_bits imm in
     let rt32 = of_int (reg2ind rt) in
     let rs32 = of_int (reg2ind rs) in
     let fields = [imm16; shift_left rt32 16; shift_left rs32 21; shift_left (of_int 0xd) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Lw(rt, rs, offset) ->
    (let offset16 = zero_top_sixteen_bits offset in
     let rt32 = of_int (reg2ind rt) in
     let rs32 = of_int (reg2ind rs) in
     let fields = [offset16; shift_left rt32 16; shift_left rs32 21; shift_left (of_int 0x23) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Sw(rt, rs, offset) ->
    (let offset16 = zero_top_sixteen_bits offset in
     let rt32 = of_int (reg2ind rt) in
     let rs32 = of_int (reg2ind rs) in
     let fields = [offset16; shift_left rt32 16; shift_left rs32 21; shift_left (of_int 0x2b) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Li(_,_) -> raise CantTranslateError

(* retrieve the opcode, first 6 bits of instruction *)
let retrieve_opcode (bin32: int32) : int32 =
  (shift_right_logical bin32 26)

(* retrieve the 2nd opcode, the last 6 bits, only used for R type instructions.
 * CS 141! *)
let retrieve_2nd_opcode (bin32: int32) : int32 =
  Int32.logand 0x0000003Fl bin32

(* get the RS register *)
let get_reg_rs (bin32: int32) : reg =
  ind2reg (Int32.logand 0x0000001Fl (shift_right_logical bin32 21))
 
(* get the RT register *)
let get_reg_rt (bin32: int32) : reg =
  ind2reg (Int32.logand 0x0000001Fl (shift_right_logical bin32 16))

(* get the RD register *)
let get_reg_rd (bin32: int32) : reg =
  ind2reg (Int32.logand 0x0000001Fl (shift_right_logical bin32 11))


