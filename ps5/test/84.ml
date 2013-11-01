let g f = (f 3, f true) in
fst (g (fun x -> x))
