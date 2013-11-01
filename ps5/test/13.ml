let g f = (f 3, f 1) in
fst (g (fun x -> x))
