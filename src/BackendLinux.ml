let verbosity = ref 0

let outfile = ref stdout

let printFlag n = !verbosity >= n

let printf x y = Printf.fprintf !outfile "%s" y; x

let printfFlush x y = Printf.fprintf !outfile "%s" y; flush !outfile; x

let lastUpdateCheck = ref (Sys.time())

let timeForStatusUpdate _ =
  if printFlag 3
  then true
  else
  let t = Sys.time() in
  if t -. !lastUpdateCheck > 5.0
  then (lastUpdateCheck := t; true)
  else false
