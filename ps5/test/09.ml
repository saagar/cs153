let f x = x in
hd (tl (tl [f 42; f 3; f 90])) = 90
