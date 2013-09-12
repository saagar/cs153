open Mips_ast
open Byte

exception TODO
exception FatalError
exception BadInstruction

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

(* Helpers to get bytes from 32 bit *)
let first_byte (x:int32) : byte = mk_byte (Int32.shift_right x 24)
let second_byte (x:int32) : byte = mk_byte (Int32.shift_right x 16)
let third_byte (x:int32) : byte = mk_byte (Int32.shift_right x 8)
let fourth_byte (x:int32) : byte = mk_byte x

(* Helper to get int32 from four bytes *)
let int32_from_bytes (byte1:byte) (byte2:byte) (byte3:byte) (byte4:byte) : int32 =
  List.fold_left Int32.logor Int32.zero [shift_left byte1.b 24; shift_left byte2.b 16; shift_left byte3.b 8; byte4.b]

(* Map a program, a list of Mips assembly instructions, down to a starting 
   state. You can start the PC at any address you wish. Just make sure that 
   you put the generated machine code where you started the PC in memory! *)
let rec assem (prog : program) : state =
  let one = Int32.one in
  let two = Int32.add one one in
  let three = Int32.add one two in
  let four = Int32.add one three in
  let load_inst (bin_inst : int32) (loc : int32) (mem : memory) : memory =
    let m1 = mem_update loc (first_byte bin_inst) mem in
    let m2 = mem_update (Int32.add one loc) (second_byte bin_inst) m1 in
    let m3 = mem_update (Int32.add two loc) (third_byte bin_inst) m2 in
    mem_update (Int32.add three loc) (fourth_byte bin_inst) m3 in
  let rec assem_helper (remaining_prog : inst list) (loc : int32) (mem : memory) : memory =
    (match remaining_prog with
      [] -> mem
    | Li(rd, imm) :: rest ->
      let eight = Int32.add four four in
      let lui = Lui(rd, grab_top_sixteen_bits imm) in
      let ori = Ori(rd, rd, zero_top_sixteen_bits imm) in
      let new_mem_1 = load_inst (inst2bin lui) loc mem in
      let new_mem_2 = load_inst (inst2bin ori) (Int32.add four loc) new_mem_1 in
      assem_helper rest (Int32.add eight loc) new_mem_2
    | inst::rest ->
      let new_mem = load_inst (inst2bin inst) loc mem in
      assem_helper rest (Int32.add four loc) new_mem) in
  { r = empty_rf; pc = four; m = assem_helper prog four empty_mem }

let disassemble (bin : int32) : inst =
  match (retrieve_opcode bin) with
    0x00l -> (match (retrieve_2nd_opcode bin) with
                | 0x08l -> Jr(get_reg_rs bin)
                | 0x20l -> Add((get_reg_rd bin),(get_reg_rs bin),(get_reg_rt bin))
                | _ -> raise BadInstruction 
              )
    | 0x03l -> Jal((zero_top_six_bits bin))
    | 0x04l -> Beq((get_reg_rs bin), (get_reg_rt bin),(zero_top_sixteen_bits bin))
    | 0x0dl -> Ori((get_reg_rt bin), (get_reg_rs bin),(zero_top_sixteen_bits
    bin))
    | 0x0fl -> Lui((get_reg_rt bin),(zero_top_sixteen_bits bin))
    | 0x23l -> Lw((get_reg_rt bin),(get_reg_rs bin),(zero_top_sixteen_bits bin))
    | 0x2bl -> Sw((get_reg_rt bin),(get_reg_rs bin),(zero_top_sixteen_bits bin))
    | _ -> raise BadInstruction
  

let execute_inst (current_state : state) : state =
  let first_inst_byte = mem_lookup current_state.pc current_state.m in
  let second_inst_byte = mem_lookup (Int32.add current_state.pc (from_int 1)) current_state.m in
  let third_inst_byte = mem_lookup (Int32.add current_state.pc (from_int 2)) current_state.m in
  let fourth_inst_byte = mem_lookup (Int32.add current_state.pc (from_int 3)) current_state.m in
  let inst32 = int32_from_bytes first_inst_byte second_inst_byte third_inst_byte fourth_inst_byte in
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

let execute_add rd rs rt current_state : state =
  let rs32 = rf_lookup (reg2ind rs) current_state.r in
  let rt32 = rf_lookup (reg2ind rt) current_state.r in
  let sum = Int32.add rs32 rt32 in
  let new_rf = rf_update (reg2ind rd) sum current_state.r in
  { r = new_rf; pc = Int32.add current_state.pc (from_int 4); m = current_state.m }

let execute_beq rs rt offset current_state : state =
  let rs32 = rf_lookup (reg2ind rs) current_state.r in
  let rt32 = rf_lookup (reg2ind rt) current_state.r in
  let amount_to_advance_pc = if (to_int rs32 = to_int rt32) then offset else from_int 4 in
  { r = current_state.r; pc = Int32.add current_state.pc amount_to_advance_pc; m = current_state.m }

let execute_jr rs current_state : state =
  let rs32 = rf_lookup (reg2ind rs) current_state.r in
  { r = current_state.r; pc = rs32; m = current_state.m }

let execute_jal target current_state : state =
  let next_inst_addr = Int32.add current_state.pc (from_int 4) in
  let new_rf = rf_update 31 next_inst_addr current_state.r in
  { r = new_rf; pc = target; m = current_state.m }

let execute_lui rt imm current_state : state =
  let new_rf = rf_update (reg2ind rt) (Int32.shift_left imm 16) current_state.r in
  { r = new_rf; pc = Int32.add current_state.pc (from_int 4); m = current_state.m }

let execute_ori rt rs imm current_state : state =
  let rs32 = rf_lookup (reg2ind rs) current_state.r in
  let new_rf = rf_update (reg2ind rt) (Int32.logor imm rs32) current_state.r in
  { r = new_rf; pc = Int32.add current_state.pc (from_int 4); m = current_state.m }

let execute_lw (rt : reg) (rs : reg) (offset : int32) (current_state : state) : state =
  let target_address = (Int32.add (rf_lookup (reg2ind rs) current_state.r) offset) in
  let byte1 = mem_lookup target_address current_state.m in
  let byte2 = mem_lookup (Int32.add target_address (from_int 1)) current_state.m in
  let byte3 = mem_lookup (Int32.add target_address (from_int 2)) current_state.m in
  let byte4 = mem_lookup (Int32.add target_address (from_int 3)) current_state.m in
  let word = int32_from_bytes byte1 byte2 byte3 byte4 in
  let new_rf = rf_update (reg2ind rt) word current_state.r in
  { r = new_rf; pc = Int32.add current_state.pc (from_int 4); m = current_state.m }

let execute_sw (rt : reg) (rs : reg) (offset : int32) (current_state : state) : state =
  let target_address = (Int32.add (rf_lookup (reg2ind rs) current_state.r) offset) in
  let value32 = rf_lookup (reg2ind rt) current_state.r in
  let byte1 = first_byte value32 in
  let byte2 = second_byte value32 in
  let byte3 = third_byte value32 in
  let byte4 = fourth_byte value32 in
  let new_mem = mem_update target_address byte1 current_state.m in
  let new_mem2 = mem_update (Int32.add target_address (from_int 1)) byte2 new_mem in
  let new_mem3 = mem_update (Int32.add target_address (from_int 2)) byte3 new_mem in
  let new_mem4 = mem_update (Int32.add target_address (from_int 3)) byte4 new_mem in
  { r = current_state.r; pc = Int32.add current_state.pc (fromt_int 4); m = new_mem4 }


(* Given a starting state, simulate the Mips machine code to get a final state *)
let rec interp (init_state : state) : state =
  let first_inst_byte = mem_lookup init_state.pc init_state.m in
  let second_inst_byte = mem_lookup (Int32.add init_state.pc (from_int 1)) init_state.m in
  let third_inst_byte = mem_lookup (Int32.add init_state.pc (from_int 2)) init_state.m in
  let fourth_inst_byte = mem_lookup (Int32.add init_state.pc (from_int 3)) init_state.m in
  let inst32 = int32_from_bytes first_inst_byte second_inst_byte third_inst_byte fourth_inst_byte in
  match to_int inst32 with
    0 -> init_state
  | _ -> interp (execute_inst init_state)
