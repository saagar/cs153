open Mips_ast
open Byte

exception TODO
exception FatalError
exception BadInstruction
exception CantTranslateError

(* Register file definitions. A register file is a map from a register 
   number to a 32-bit quantity. *)
module IntMap = Map.Make(struct type t = int let compare = compare end)
type regfile = int32 IntMap.t 
let empty_rf = IntMap.empty
let rf_update (r : int) (v : int32) (rf : regfile) : regfile = 
  IntMap.add r v rf
let rf_lookup (r : int) (rf : regfile) : int32 = 
  try IntMap.find r rf with Not_found -> Int32.zero
let string_of_rf (rf : regfile) : string = 
  IntMap.fold (fun key v s -> 
    s^(string_of_int key)^" -> "^(Int32.to_string v)^"\n") rf ""

(* Memory definitions. A memory is a map from 32-bit addresses to bytes. *)
module Int32Map = Map.Make(struct type t = int32 let compare = Int32.compare end)
type memory = byte Int32Map.t
let empty_mem = Int32Map.empty
let mem_update (a : int32) (v : byte) (m : memory) : memory =
  Int32Map.add a v m
let mem_lookup (a : int32) (m : memory) : byte =
  try (Int32Map.find a m) with Not_found -> mk_byte Int32.zero
let string_of_mem (m : memory) : string =
  Int32Map.fold (fun key v s ->
    s^(Int32.to_string key)^" -> "^(Int32.to_string (b2i32 v))^"\n") m ""

(* State *)
type state = { r : regfile; pc : int32; m : memory }

(* Helper to get bytes from 32 bit *)
let bytes_from_int32 (x:int32) : byte * byte * byte * byte =
  (mk_byte (Int32.shift_right x 24), mk_byte (Int32.shift_right x 16), mk_byte (Int32.shift_right x 8), mk_byte x)

(* Helper to get int32 from four bytes *)
let int32_from_bytes (bytes : byte * byte * byte * byte) : int32 =
  let (byte1, byte2, byte3, byte4) = bytes in
  List.fold_left Int32.logor Int32.zero [Int32.shift_left byte1.b 24; Int32.shift_left byte2.b 16; Int32.shift_left byte3.b 8; byte4.b]

let zero_top_24_bits (x:int32) : int32 =
  Int32.logand 0x000000FFl x

let zero_top_sixteen_bits (x:int32) : int32 =
  Int32.logand 0x0000FFFFl x

let zero_top_six_bits (x:int32) : int32 =
  Int32.logand 0x03FFFFFFl x

let grab_top_sixteen_bits (x:int32) : int32 =
  Int32.shift_right_logical x 16

(* assembles a single instruction *)
let inst2bin (i:inst) : int32 =
  match i with
    Add(rd, rs, rt) ->
      (let rd32 = Int32.of_int (reg2ind rd) in
       let rs32 = Int32.of_int (reg2ind rs) in
       let rt32 = Int32.of_int (reg2ind rt) in
       let fields = [Int32.of_int 0x20; Int32.shift_left rd32 11; Int32.shift_left rt32 16; Int32.shift_left rs32 21] in
       List.fold_left Int32.logor Int32.zero fields)
  | Beq(rs, rt, offset) ->
    (let rs32 = Int32.of_int (reg2ind rs) in
     let rt32 = Int32.of_int (reg2ind rt) in
     let offset16 = zero_top_sixteen_bits offset in
     let fields = [offset16; Int32.shift_left rt32 16; Int32.shift_left rs32 21; Int32.shift_left (Int32.of_int 4) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Jr(rs) ->
    (let rs32 = Int32.of_int (reg2ind rs) in
     let fields = [Int32.of_int 8; Int32.shift_left rs32 21] in
     List.fold_left Int32.logor Int32.zero fields)
  | Jal(target) ->
    (let target26 = zero_top_six_bits target in
     let fields = [target26; Int32.shift_left (Int32.of_int 3) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Lui(rt, imm) ->
    (let imm16 = zero_top_sixteen_bits imm in
     let rt32 = Int32.of_int (reg2ind rt) in
     let fields = [imm16; Int32.shift_left rt32 16; Int32.shift_left (Int32.of_int 0xf) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Ori(rt, rs, imm) ->
    (let imm16 = zero_top_sixteen_bits imm in
     let rt32 = Int32.of_int (reg2ind rt) in
     let rs32 = Int32.of_int (reg2ind rs) in
     let fields = [imm16; Int32.shift_left rt32 16; Int32.shift_left rs32 21; Int32.shift_left (Int32.of_int 0xd) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Lw(rt, rs, offset) ->
    (let offset16 = zero_top_sixteen_bits offset in
     let rt32 = Int32.of_int (reg2ind rt) in
     let rs32 = Int32.of_int (reg2ind rs) in
     let fields = [offset16; Int32.shift_left rt32 16; Int32.shift_left rs32 21; Int32.shift_left (Int32.of_int 0x23) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Sw(rt, rs, offset) ->
    (let offset16 = zero_top_sixteen_bits offset in
     let rt32 = Int32.of_int (reg2ind rt) in
     let rs32 = Int32.of_int (reg2ind rs) in
     let fields = [offset16; Int32.shift_left rt32 16; Int32.shift_left rs32 21; Int32.shift_left (Int32.of_int 0x2b) 26] in
     List.fold_left Int32.logor Int32.zero fields)
  | Li(_,_) -> raise CantTranslateError (* li is a pseudoinstruction, handle it before calling this function *)

(* retrieve the opcode, first 6 bits of instruction *)
let retrieve_opcode (bin32: int32) : int32 =
  (Int32.shift_right_logical bin32 26)

(* retrieve the 2nd opcode, the last 6 bits, only used for R type instructions.
 * CS 141! *)
let retrieve_2nd_opcode (bin32: int32) : int32 =
  Int32.logand 0x0000003Fl bin32

(* get the RS register *)
let get_reg_rs (bin32: int32) : reg =
  ind2reg (Int32.logand 0x0000001Fl (Int32.shift_right_logical bin32 21))
 
(* get the RT register *)
let get_reg_rt (bin32: int32) : reg =
  ind2reg (Int32.logand 0x0000001Fl (Int32.shift_right_logical bin32 16))

(* get the RD register *)
let get_reg_rd (bin32: int32) : reg =
  ind2reg (Int32.logand 0x0000001Fl (Int32.shift_right_logical bin32 11))

(* updates four bytes in succession in memory *)
let mem_update_word (loc:int32) (bytes:byte*byte*byte*byte) (m:memory) : memory =
  let (byte1, byte2, byte3, byte4) = bytes in
  let m1 = mem_update loc byte1 m in
  let m2 = mem_update (Int32.add (Int32.of_int 1) loc) byte2 m1 in
  let m3 = mem_update (Int32.add (Int32.of_int 2) loc) byte3 m2 in
  mem_update (Int32.add (Int32.of_int 3) loc) byte4 m3

(* grabs four bytes in succession from memory *)
let mem_lookup_word (loc:int32) (m:memory) : byte*byte*byte*byte =
  let byte1 = mem_lookup loc m in
  let byte2 = mem_lookup (Int32.add loc (Int32.of_int 1)) m in
  let byte3 = mem_lookup (Int32.add loc (Int32.of_int 2)) m in
  let byte4 = mem_lookup (Int32.add loc (Int32.of_int 3)) m in
  (byte1, byte2, byte3, byte4)

(* Map a program, a list of Mips assembly instructions, down to a starting 
   state. You can start the PC at any address you wish. Just make sure that 
   you put the generated machine code where you started the PC in memory! *)
let rec assem (prog : program) : state =
  let load_inst (bin_inst : int32) (loc : int32) (mem : memory) : memory =
    mem_update_word loc (bytes_from_int32 bin_inst) mem in
  let rec assem_helper (remaining_prog : inst list) (loc : int32) (mem : memory) : memory =
    (match remaining_prog with
      [] -> mem
    | Li(rd, imm) :: rest ->
      let lui = Lui(rd, grab_top_sixteen_bits imm) in
      let ori = Ori(rd, rd, zero_top_sixteen_bits imm) in
      let new_mem_1 = load_inst (inst2bin lui) loc mem in
      let new_mem_2 = load_inst (inst2bin ori) (Int32.add (Int32.of_int 4) loc) new_mem_1 in
      assem_helper rest (Int32.add (Int32.of_int 8) loc) new_mem_2
    | inst::rest ->
      let new_mem = load_inst (inst2bin inst) loc mem in
      assem_helper rest (Int32.add (Int32.of_int 4) loc) new_mem) in
  { r = empty_rf; pc = (Int32.of_int 4); m = assem_helper prog (Int32.of_int 4) empty_mem }

(* reverse of inst2bin *)
let disassemble (bin : int32) : inst =
  match (retrieve_opcode bin) with
    0x00l -> (match (retrieve_2nd_opcode bin) with
    | 0x08l -> Jr(get_reg_rs bin)
    | 0x20l -> Add((get_reg_rd bin), (get_reg_rs bin), (get_reg_rt bin))
    | _ -> raise BadInstruction)
  | 0x03l -> Jal((zero_top_six_bits bin))
  | 0x04l -> Beq((get_reg_rs bin), (get_reg_rt bin), (zero_top_sixteen_bits bin))
  | 0x0dl -> Ori((get_reg_rt bin), (get_reg_rs bin), (zero_top_sixteen_bits bin))
  | 0x0fl -> Lui((get_reg_rt bin), (zero_top_sixteen_bits bin))
  | 0x23l -> Lw((get_reg_rt bin), (get_reg_rs bin), (zero_top_sixteen_bits bin))
  | 0x2bl -> Sw((get_reg_rt bin), (get_reg_rs bin), (zero_top_sixteen_bits bin))
  | _ -> raise BadInstruction

(* helper function used for int32s being used to simulate int16s (i.e. top 16 bits are zero). if the 16th bit is set, subtract 2^16 to get a negative value *)
let twos_complement_16bit (x:int32) : int32 =
  if (Int32.to_int x >= 32768) then Int32.of_int ((Int32.to_int x) - 65536) else x

let execute_add rd rs rt current_state : state =
  let rs32 = rf_lookup (reg2ind rs) current_state.r in
  let rt32 = rf_lookup (reg2ind rt) current_state.r in
  let sum = Int32.add rs32 rt32 in
  let new_rf = rf_update (reg2ind rd) sum current_state.r in
  { r = new_rf; pc = Int32.add current_state.pc (Int32.of_int 4); m = current_state.m }

(* no delay slots, i.e. if $rs = $rt we jump [offset] instructions, not [sffset + 1] instructions *)
let execute_beq rs rt offset current_state : state =
  let rs32 = rf_lookup (reg2ind rs) current_state.r in
  let rt32 = rf_lookup (reg2ind rt) current_state.r in
  let signed_offset = twos_complement_16bit offset in
  let amount_to_advance_pc = if (Int32.to_int rs32 = Int32.to_int rt32) then (Int32.shift_left signed_offset 2) else Int32.of_int 4 in
  { r = current_state.r; pc = Int32.add current_state.pc amount_to_advance_pc; m = current_state.m }

let execute_jr rs current_state : state =
  let rs32 = rf_lookup (reg2ind rs) current_state.r in
  { r = current_state.r; pc = rs32; m = current_state.m }

(* target is left-shifted by 2 per greg's piazza response *)
let execute_jal target current_state : state =
  let next_inst_addr = Int32.add current_state.pc (Int32.of_int 4) in
  let new_rf = rf_update 31 next_inst_addr current_state.r in
  { r = new_rf; pc = Int32.shift_left target 2; m = current_state.m }

let execute_lui rt imm current_state : state =
  let new_rf = rf_update (reg2ind rt) (Int32.shift_left imm 16) current_state.r in
  { r = new_rf; pc = Int32.add current_state.pc (Int32.of_int 4); m = current_state.m }

let execute_ori rt rs imm current_state : state =
  let rs32 = rf_lookup (reg2ind rs) current_state.r in
  let new_rf = rf_update (reg2ind rt) (Int32.logor imm rs32) current_state.r in
  { r = new_rf; pc = Int32.add current_state.pc (Int32.of_int 4); m = current_state.m }

let execute_lw (rt : reg) (rs : reg) (offset : int32) (current_state : state) : state =
  let signed_offset = twos_complement_16bit offset in
  let target_address = (Int32.add (rf_lookup (reg2ind rs) current_state.r) signed_offset) in
  let word = int32_from_bytes (mem_lookup_word target_address current_state.m) in
  let new_rf = rf_update (reg2ind rt) word current_state.r in
  { r = new_rf; pc = Int32.add current_state.pc (Int32.of_int 4); m = current_state.m }

let execute_sw (rt : reg) (rs : reg) (offset : int32) (current_state : state) : state =
  let signed_offset = twos_complement_16bit offset in
  let target_address = (Int32.add (rf_lookup (reg2ind rs) current_state.r) signed_offset) in
  let value32 = rf_lookup (reg2ind rt) current_state.r in
  let new_mem = mem_update_word target_address (bytes_from_int32 value32) current_state.m in
  { r = current_state.r; pc = Int32.add current_state.pc (Int32.of_int 4); m = new_mem }

(* simulate one instruction. handle the stop instruction (0x0) elsewhere *)
let interp_step (current_state : state) : state =
  let inst32 = int32_from_bytes (mem_lookup_word current_state.pc current_state.m) in
  match disassemble inst32 with
    Add(rd, rs, rt) -> execute_add rd rs rt current_state
  | Beq(rs, rt, offset) -> execute_beq rs rt offset current_state
  | Jr(rs) -> execute_jr rs current_state
  | Jal(target) -> execute_jal target current_state
  | Lui(rt, imm) -> execute_lui rt imm current_state
  | Ori(rt, rs, imm) -> execute_ori rt rs imm current_state
  | Lw(rt, rs, offset) -> execute_lw rt rs offset current_state
  | Sw(rt, rs, offset) -> execute_sw rt rs offset current_state
  | Li(_,_) -> raise CantTranslateError

(* Given a starting state, simulate the Mips machine code to get a final state *)
let rec interp (init_state : state) : state =
  let inst32 = int32_from_bytes (mem_lookup_word init_state.pc init_state.m) in
  match Int32.to_int inst32 with
    0 -> init_state (* halt *)
  | _ -> interp (interp_step init_state)
