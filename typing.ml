
type 'a typp = Int | Uint | Long | Bool | Unit | Fun of 'a typp * 'a typp
  | Typvar of 'a

module Typvar = struct

type t = r BatUref.t and r = { id: int; mutable def: t typp option }

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

type typ = Typvar.t typp

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

let rec unify_vars v w =
  let sel a b =
    match a.Typvar.def, b.Typvar.def with
    | None, _ -> b
    | _, None -> a
    | Some t, Some t' ->
      if occur v t' || occur w t then raise Recursive_type;
      unify t t';
      a
  in
  if not (Typvar.equal v w) then BatUref.unite ~sel v w

and unify t t' =
  let def v t =
    match Typvar.def v with
    | None -> Typvar.define v t
    | Some x -> unify t x
  in
  match t, t' with
  | Int, Int | Uint, Uint | Long, Long | Bool, Bool | Unit, Unit -> ()
  | Fun (t1, t2), Fun (t1', t2') -> unify t1 t1';
                                    unify t2 t2'
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
  | Typvar v, Typvar w -> unify_vars v w
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
  shape: typ
}

let free_vars_of_scheme s = Typvars.diff (free_vars_of_typ s.shape) s.qual

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

type annot = int typp

let typ_of_annot a =
  let h = Hashtbl.create 0 in
  let v i =
    try Hashtbl.find h i with Not_found ->
      let v = Typvar.fresh() in
      Hashtbl.add h i v; v
  in
  let rec f = function
  | Int -> Int
  | Uint -> Uint
  | Long -> Long
  | Bool -> Bool
  | Unit -> Unit
  | Fun (t1, t2) -> Fun (f t1, f t2)
  | Typvar i -> Typvar (v i)
  in
  f a

let class_of_annot a =
  let h = Hashtbl.create 0 in
  let v i =
    try Hashtbl.find h i with Not_found ->
      let v = Typvar.fresh() in
      Hashtbl.add h i v; v
  in
  let rec f = function
  | Int | Uint | Long -> Int
  | Bool -> Bool
  | Unit -> Unit
  | Fun (t1, t2) -> Fun (f t1, f t2)
  | Typvar i -> Typvar (v i)
  in
  f a

type parm = string * annot option

type expr =
| Let of string * annot option * expr
| Var of string * annot option * expr
| Ident of string
| Annot of expr * annot
| Letfun of string * parm list * expr
| Assign of expr * expr
| Apply of expr * expr
| Sum of expr * expr
| Eq of expr * expr
| Lt of expr * expr
| If of expr * expr * expr
| Seq of expr * expr
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

type tparm = string * annot option

type e =
| TLet of string * annot option * texpr
| TVar of string * annot option * texpr
| TIdent of string
| TAnnot of texpr * annot
| TLetfun of string * tparm list * texpr
| TAssign of texpr * texpr
| TApply of texpr * texpr
| TSum of texpr * texpr
| TEq of texpr * texpr
| TLt of texpr * texpr
| TIf of texpr * texpr * texpr
| TSeq of texpr * texpr
| TConst of int
| TVoid

and texpr = { expr: e; typ: typ }

module Env = Map.Make(String)

let free_vars_of_env env =
  Env.fold (fun _ schm set ->
    Typvars.union set (free_vars_of_scheme schm)) env Typvars.empty

let mono t = { qual = Typvars.empty; shape = t }

let poly env t =
  let qual = Typvars.diff (free_vars_of_typ t) (free_vars_of_env env) in
  { qual; shape = t }

let rec infer env expr =
  match expr with
  | Void -> { expr = TVoid; typ = Unit }, env
  | Const c -> { expr = TConst c; typ = Int }, env
  | Ident id ->
    let schm = Env.find id env in
    { expr = TIdent id; typ = instance schm }, env
  | Seq (e1, e2) ->
    let te1, env1 = infer env e1 in
    let te2, env2 = infer env1 e2 in
    { expr = TSeq (te1, te2); typ = te2.typ }, env2
  | Eq (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    unify te1.typ te2.typ;
    { expr = TEq (te1, te2); typ = Bool }, env
  | Sum (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    unify te1.typ Int;
    unify te2.typ Int;
    { expr = TSum (te1, te2); typ = Int }, env
  | Var (id, annot, e) ->
    let te, _ = infer env e in
    begin match annot with
    | Some a -> unify te.typ (class_of_annot a)
    | None -> ()
    end;
    let schm = mono te.typ in
    let env = Env.add id schm env in
    { expr = TVar (id, annot, te); typ = Unit }, env
  | Let (id, annot, e) ->
    let te, _ = infer env e in
    begin match annot with
    | Some a -> unify te.typ (class_of_annot a)
    | None -> ()
    end;
    let schm = poly env te.typ in
    let env = Env.add id schm env in
    { expr = TLet (id, annot, te); typ = Unit }, env


  | _ -> { expr = TVoid; typ = Unit }, env


