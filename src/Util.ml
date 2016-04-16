open PipeGraph

let rec pipegraphStringHelper s n l =
  try
    pipegraphStringHelper s (n+1) (String.get s n :: l)
  with Invalid_argument _ ->
    List.rev_append l []

let pipegraphString s = pipegraphStringHelper s 0 []
