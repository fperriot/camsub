
type 'a typ = Int | Uint | Long | Bool | Unit | Fun of 'a typ * 'a typ
  | Typvar of 'a

type 'a annot = 'a typ

type 'a parm = string * 'a annot option

type 'a expr =
| Let of string * 'a annot option * 'a expr
| Var of string * 'a annot option * 'a expr
| Ident of string
| Annot of 'a expr * 'a annot
| Letfun of string * 'a parm list * 'a expr
| Assign of 'a expr * 'a expr
| Apply of 'a expr * 'a expr
| Sum of 'a expr * 'a expr
| Eq of 'a expr * 'a expr
| Lt of 'a expr * 'a expr
| If of 'a expr * 'a expr * 'a expr
| Seq of 'a expr * 'a expr
| Const of int

(*
  let f (x : int) y (z : uint) = if x < y then x + y else x + z
*)

let test1 =
  Letfun ("f", [("x", Some Int); ("y", None); ("z", Some Uint)],
    If (Lt (Ident "x", Ident "y"),
      Sum (Ident "x", Ident "y"),
      Sum (Ident "x", Ident "z")))

module Typed = struct

type 'a parm = string * 'a typ

type 'a e =
| Let of string * 'a typ * 'a expr
| Var of string * 'a typ * 'a expr
| Ident of string
| Letfun of string * 'a parm list * 'a expr
| Assign of 'a expr * 'a expr
| Apply of 'a expr * 'a expr
| Sum of 'a expr * 'a expr
| Eq of 'a expr * 'a expr
| Lt of 'a expr * 'a expr
| If of 'a expr * 'a expr * 'a expr
| Seq of 'a expr * 'a expr
| Const of int

and 'a expr = { expr: 'a e; typ: 'a typ }

end

(* this would require -rectypes
type typvar = typvar typ option BatUref.t
*)

type typvar = TV of typvar typ option BatUref.t

let fresh_typvar () = TV (BatUref.uref None)

let rec occur (TV v) t =
  match t with
  | Int | Uint | Long | Bool | Unit -> false
  | Fun (t1, t2) -> occur (TV v) t1 || occur (TV v) t2
  | Typvar (TV w) ->
    match BatUref.uget w with
    | None -> BatUref.equal v w
    | Some t' -> BatUref.equal v w || occur (TV v) t'

exception Unification_failure
exception Recursive_type

let rec unify (TV v) (TV w) =
  let sel vdef wdef =
    match vdef, wdef with
    | None, _ -> wdef
    | _, None -> vdef
    | Some t, Some t' ->
      if occur (TV v) t' || occur (TV w) t then
        raise Recursive_type;
      unify_types t t';
      vdef
  in
  BatUref.unite ~sel v w

and unify_types t t' =
  let def v t =
    match BatUref.uget v with
    | None -> BatUref.uset v (Some t)
    | Some d -> unify_types t d
  in
  match t, t' with
  | Int, Int | Uint, Uint | Long, Long | Bool, Bool | Unit, Unit -> ()
  | Fun (t1, t2), Fun (t1', t2') -> unify_types t1 t1';
                                    unify_types t2 t2'
  | Int, Typvar (TV v)
  | Uint, Typvar (TV v)
  | Long, Typvar (TV v)
  | Bool, Typvar (TV v)
  | Unit, Typvar (TV v)
  | Fun _, Typvar (TV v) -> def v t
  | Typvar (TV v), Int
  | Typvar (TV v), Uint
  | Typvar (TV v), Long
  | Typvar (TV v), Bool
  | Typvar (TV v), Unit
  | Typvar (TV v), Fun _ -> def v t'
  | Typvar (TV v), Typvar (TV w) -> unify (TV v) (TV w)
  | Int, _ | Uint, _ | Long, _ | Bool, _ | Unit, _ | Fun _, _ ->
    raise Unification_failure

type typvars
