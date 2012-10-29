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

module Fixpoint(F: sig type t val eq: t -> t -> bool val f: t -> t end) =
struct
let rec from init =
  let next = F.f init in
  if F.eq next init then init else from next
end

