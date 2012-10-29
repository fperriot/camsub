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

module Fixpoint(Dom: sig type t val eq: t -> t -> bool end) =
struct
let rec fix f v =
  let x = f v in
  if Dom.eq x v then v else fix f x
end

