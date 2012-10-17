
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
| Void

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
| Void

and 'a expr = { expr: 'a e; typ: 'a typ }

end

module Typvar = struct

type t = r BatUref.t and r = { id: int; mutable def: t typ option }

let counter = ref 0

let fresh () =
  let id = !counter in
  incr counter;
  BatUref.uref { id; def = None }

let id v = (BatUref.uget v).id

let def v = (BatUref.uget v).def

let define v t = (BatUref.uget v).def <- Some t

let compare a b = Pervasives.compare (id a) (id b)

let equal = BatUref.equal

let hash = id

end

let rec occur v t =
  match t with
  | Int | Uint | Long | Bool | Unit -> false
  | Fun (t1, t2) -> occur v t1 || occur v t2
  | Typvar w ->
    match Typvar.def w with
    | None -> Typvar.equal v w
    | Some t' -> Typvar.equal v w || occur v t'

exception Unification_failure
exception Recursive_type

let rec unify v w =
  let sel a b =
    match a.Typvar.def, b.Typvar.def with
    | None, _ -> b
    | _, None -> a
    | Some t, Some t' ->
      if occur v t' || occur w t then raise Recursive_type;
      unify_types t t';
      a
  in
  if not (Typvar.equal v w) then BatUref.unite ~sel v w

and unify_types t t' =
  let def v t =
    match Typvar.def v with
    | None -> Typvar.define v t
    | Some x -> unify_types t x
  in
  match t, t' with
  | Int, Int | Uint, Uint | Long, Long | Bool, Bool | Unit, Unit -> ()
  | Fun (t1, t2), Fun (t1', t2') -> unify_types t1 t1';
                                    unify_types t2 t2'
  | Int, Typvar v
  | Uint, Typvar v
  | Long, Typvar v
  | Bool, Typvar v
  | Unit, Typvar v
  | Fun _, Typvar v -> def v t
  | Typvar v, Int
  | Typvar v, Uint
  | Typvar v, Long
  | Typvar v, Bool
  | Typvar v, Unit
  | Typvar v, Fun _ -> def v t'
  | Typvar v, Typvar w -> unify v w
  | Int, _ | Uint, _ | Long, _ | Bool, _ | Unit, _ | Fun _, _ ->
    raise Unification_failure

module Typvars = Set.Make(Typvar)

let rec free_vars_of_typ = function
  | Int | Uint | Long | Bool | Unit -> Typvars.empty
  | Fun (t1, t2) -> Typvars.union (free_vars_of_typ t1)
                                  (free_vars_of_typ t2)
  | Typvar v ->
    match Typvar.def v with
    | None -> Typvars.singleton v
    | Some t -> free_vars_of_typ t

type scheme = {
  qual: Typvars.t;    (* Universally qualified type variables *)
  shape: Typvar.t typ
}

(* instantiate a type scheme by replacing all universally qualified type
   variables occuring in the scheme with fresh type vars *)

module H = Hashtbl.Make(Typvar)

let instance schm =
  let n = Typvars.cardinal schm.qual in
  let h = H.create n in
  Typvars.iter (fun v -> H.add h v (Typvar.fresh())) schm.qual;
  let rec inst t =
    match t with
    | Int | Uint | Long | Bool | Unit -> t
    | Fun (t1, t2) -> Fun (inst t1, inst t2)
    | Typvar v -> Typvar (try H.find h v with Not_found -> v)
  in
  inst schm.shape

(* TODO
  - Maintain an environment associating variable names with type schemes
  - As part of the env, maintain a set of free variables occuring in the
    type schemes of all previous expressions
  - When infering the type of a let-expression, generalize the type vars
    appearing free in the monotype and not free in the env
 *)

let class_of_var = H.create 0

let alloc_var_pair() =
  let v = Typvar.fresh() in
  let w = Typvar.fresh() in
  H.add class_of_var v w;
  v, w

let rec class_of_typ = function
  | Int | Uint | Long -> Int
  | Bool -> Bool
  | Unit -> Unit
  | Fun (t1, t2) -> Fun (class_of_typ t1, class_of_typ t2)
  | Typvar v -> Typvar (H.find class_of_var v)

let unify_classes t t' =
  unify_types (class_of_typ t) (class_of_typ t')

module Env = Map.Make(String)

let constraints = ref []

let unify_weak t t' =
  unify_classes t t';
  constraints := (t, t') :: !constraints

let rec infer env expr =
  let module T = Typed in
  match expr with
  | Void -> { T.expr = T.Void; typ = Unit }, env
  | Const c ->
    let v, w = alloc_var_pair() in
    Typvar.define w Int;
    { T.expr = T.Const c; typ = Typvar v }, env
  | Ident id ->
    { T.expr = T.Ident id; typ = Env.find id env }, env
  | Seq (e1, e2) ->
    let te1, env1 = infer env e1 in
    let te2, env2 = infer env1 e2 in
    { T.expr = T.Seq (te1, te2); typ = te2.T.typ }, env2
  | Eq (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    unify_weak te1.T.typ te2.T.typ;
    { T.expr = T.Eq (te1, te2); typ = Bool }, env
  | Sum (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    unify_classes te1.T.typ Int;
    unify_weak te1.T.typ te2.T.typ;
    let v, w = alloc_var_pair() in
    Typvar.define w Int;

  | _ -> { T.expr = T.Void; typ = Unit }, env

