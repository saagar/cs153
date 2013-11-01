let x = if true then 10 else 20 in
let y = if false then 15 else 25 in
let z = if (x = y) then 3 else 4 in
let m = (fst (100, 200) = 100) in
let n = (snd (300, 400) = 300) in
if m then (x + y + z) else (if n then (x * y * z) else 50)
