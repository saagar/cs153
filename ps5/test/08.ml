let f x = x in
isnil (tl (tl (tl [f 42; f 3; f 90])))
