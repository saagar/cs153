let execute_ori rt rs imm current_state : state =
  let rs32 = rf_lookup (reg2ind rs) current_state.r in
  let new_rf = rf_update (reg2ind rt) (Int32.logor imm rs32) current_state.r in
  { r = new_rf; pc = Int32.add current_state.pc (from_int 4); m =
    current_state.m }

let execute_lui rt imm current_state : state =
  let new_rf = rf_update (reg2ind rt) (Int32.shift_left imm 16) current_state.r
  in
  { r = new_rf; pc = Int32.add current_state.pc (from_int 4); m =
    current_state.m }

let execute_lw (rt : reg) (rs : reg) (offset : int32) (current_state : state) : state =
  let target_address = (Int32.add (rf_lookup (reg2ind rs) current_state.r)
  offset) in
  let new_rf = rf_update (reg2ind rt) (mem_lookup target_address current_state.m) current_state.r in
  { r = new_rf; pc = Int32.add current_state.pc (from_int 4); m =
    current_state.m }

let execute_sw (rt : reg) (rs : reg) (offset : int32) (current_state : state) :
  state =
    let target_address = (Int32.add (rf_lookup (reg2ind rs) current_state.r)
    offset) in
    let new_mem = mem_update target_address (rf_lookup (reg2ind rt)
    current_state.r) current_state.m  in
    { r = current_state.r; pc = Int32.add current_state.pc (fromt_int 4); m =
      new_mem }
