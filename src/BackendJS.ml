let verbosity = ref 0

let outfile = ref stdout

let printFlag n = !verbosity >= n

let printf x y =
  Js.Unsafe.fun_call (Js.Unsafe.js_expr "hello")
    [|Js.Unsafe.inject (Js.string y)|];
  x

let printfFlush x y =
  printf x y

let lastUpdateCheck = ref (Sys.time())

let timeForStatusUpdate _ =
  let t = Sys.time() in
  if t -. !lastUpdateCheck > 1.0
  then (lastUpdateCheck := t; true)
  else false
