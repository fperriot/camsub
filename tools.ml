(* merge two sorted lists with no dups into one sorted list with no dups *)

let merge a b =
  let rec loop a b acc =
    match a with
    | [] -> List.rev_append acc b
    | x :: a' ->
      match b with
      | [] -> List.rev_append acc a
      | y :: b' ->
        if x = y then loop a' b' (x :: acc) else
        if x < y then loop a' b (x :: acc) else
                      loop a b' (y :: acc)
  in
  loop a b []

let filter_revmap f =
  List.fold_left (fun acc x -> match f x with Some r -> r :: acc
                                            | None -> acc) []


