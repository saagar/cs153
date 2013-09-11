open Mips_ast
open Byte

exception TODO
exception FatalError

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
      let new_mem_1 = load_inst (inst2bin Lui(rd, grab_top_sixteen_bits imm)) loc mem in
      let new_mem_2 = load_inst (inst2bin Ori(rd, rd, zero_top_sixteen_bits imm)) (Int32.add four loc) new_mem_1 in
      assem_helper rest (Int32.add eight loc) new_mem_2
    | inst::rest ->
      let new_mem = load_inst (inst2bin inst) loc mem in
      assem_helper rest (Int32.add four loc) new_mem) in
  { r = empty_rf; pc = four; m = assem_helper prog four empty_mem }

(* Given a starting state, simulate the Mips machine code to get a final state *)
let rec interp (init_state : state) : state = raise TODO
