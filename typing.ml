
type 'a typp = Int | Uint | Long | Bool | Unit | Fun of 'a typp * 'a typp
  | Typvar of 'a

module Typvar = struct

type t = r BatUref.t and r = { id: int;
                               mutable def: t typp option;
                               num: bool BatUref.t }
let counter = ref 0

let fresh () =
  let id = !counter in
  incr counter;
  let num = BatUref.uref false in
  BatUref.uref { id; def = None; num }

let id v = (BatUref.uget v).id
let def v = (BatUref.uget v).def
let num v = BatUref.uget (BatUref.uget v).num

let restrict v = BatUref.uset (BatUref.uget v).num true

let define v t = (BatUref.uget v).def <- Some t

let compare a b = Pervasives.compare (id a) (id b)

let equal = BatUref.equal

let hash = id

end

type typ = Typvar.t typp

(*
let deref = function
  | Typvar v -> (match Typvar.def v with Some t -> t | None -> Typvar v)
  | t -> t
*)

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

let rec unify ?(weak=true) t t' =
  let var_with_numeric v t =
    match Typvar.def v with
    | None ->
      Typvar.restrict v;
      if not weak then Typvar.define v t
    | Some t' ->
      unify ~weak t t'
  in
  let var_with_nonnumeric v t =
    if Typvar.num v then raise Unification_failure;
    match Typvar.def v with
    | None ->
      if occur v t then raise Recursive_type;
      Typvar.define v t
    | Some t' ->
      unify ~weak:false t t'
  in
  match t, t' with
  | Int, Int
  | Uint, Uint
  | Long, Long
  | Bool, Bool
  | Unit, Unit -> ()
  | Int, Uint
  | Int, Long
  | Uint, Int
  | Uint, Long
  | Long, Int
  | Long, Uint -> if not weak then raise Unification_failure
  | Fun (t1, t2), Fun (t1', t2') -> unify ~weak:false t1 t1';
                                    unify ~weak:false t2 t2'
  | Int, Typvar v
  | Uint, Typvar v
  | Long, Typvar v -> var_with_numeric v t
  | Bool, Typvar v
  | Unit, Typvar v
  | Fun _, Typvar v -> var_with_nonnumeric v t
  | Typvar v, Int
  | Typvar v, Uint
  | Typvar v, Long -> var_with_numeric v t'
  | Typvar v, Bool
  | Typvar v, Unit
  | Typvar v, Fun _ -> var_with_nonnumeric v t'
  | Typvar v, Typvar w ->
    if not (Typvar.equal v w) then begin
      let rv = BatUref.uget v in
      let rw = BatUref.uget w in
      BatUref.unite ~sel:( || ) rv.Typvar.num rw.Typvar.num;
      match rv.Typvar.def, rw.Typvar.def with
      | None, None -> if not weak then BatUref.unite v w
      | Some t, None -> unify ~weak t t'
      | None, Some t' -> unify ~weak t t'
      | Some t, Some t' -> unify ~weak t t'
    end
  | Int, _
  | Uint, _
  | Long, _
  | Bool, _
  | Unit, _
  | Fun _, _ -> raise Unification_failure

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

and texpr = { expr: e; cls:typ; typ: typ }

module Env = Map.Make(String)

let free_vars_of_env f env =
  Env.fold (fun _ schm set ->
    Typvars.union set (free_vars_of_scheme (f schm))) env Typvars.empty

let mono t = { qual = Typvars.empty; shape = t }

let poly f env t =
  let qual = Typvars.diff (free_vars_of_typ t) (free_vars_of_env f env) in
  { qual; shape = t }

let rec infer env expr =
  match expr with
  | Void -> { expr = TVoid; cls = Unit;
                            typ = Unit }, env
  | Const c -> { expr = TConst c; cls = Int;
                                  typ = Typvar (Typvar.fresh()) }, env
  | Ident id ->
    let schm = Env.find id env in
    { expr = TIdent id; cls = instance (fst schm);
                        typ = instance (snd schm) }, env
  | Seq (e1, e2) ->
    let te1, env1 = infer env e1 in
    let te2, env2 = infer env1 e2 in
    { expr = TSeq (te1, te2); cls = te2.cls;
                              typ = te2.typ }, env2
  | Eq (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    unify te1.cls te2.cls;
    { expr = TEq (te1, te2); cls = Bool;
                             typ = Bool }, env
  | Sum (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    unify te1.cls Int;
    unify te2.cls Int;
    { expr = TSum (te1, te2); cls = Int;
                              typ = Typvar (Typvar.fresh()) }, env
  | Var (id, annot, e) ->
    let te, _ = infer env e in
    begin match annot with
    | Some a -> unify te.cls (class_of_annot a);
                unify te.typ (typ_of_annot a)
    | None -> ()
    end;
    let schm = (mono te.cls, mono te.typ) in
    let env = Env.add id schm env in
    { expr = TVar (id, annot, te); cls = Unit;
                                   typ = Unit }, env
  | Let (id, annot, e) ->
    let te, _ = infer env e in
    begin match annot with
    | Some a -> unify te.cls (class_of_annot a);
                unify te.typ (typ_of_annot a)
    | None -> ()
    end;
    let schm = (poly fst env te.cls, poly snd env te.typ) in
    let env = Env.add id schm env in
    { expr = TLet (id, annot, te); cls = Unit;
                                   typ = Unit }, env


  | _ -> { expr = TVoid; cls = Unit; typ = Unit }, env


