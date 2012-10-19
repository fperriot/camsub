
type 'a typp = Int | Uint | Long | Bool | Unit | Fun of 'a typp * 'a typp
  | Typvar of 'a

module Typvar = struct

type t = r BatUref.t and r = { id: int;
                               mutable def: t typp option;
                               num: bool BatUref.t }
let counter = ref 0

let fresh ?(numeric=false) () =
  let id = !counter in
  incr counter;
  let num = BatUref.uref numeric in
  BatUref.uref { id; def = None; num }

let fresh_num () = fresh ~numeric:true ()

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

let deref = function
  | Typvar v -> (match Typvar.def v with Some t -> t | None -> Typvar v)
  | t -> t

let rec occur v t =
  assert (Typvar.def v = None);
  match deref t with
  | Int | Uint | Long | Bool | Unit -> false
  | Fun (t1, t2) -> occur v t1 || occur v t2
  | Typvar w -> Typvar.equal v w

exception Unification_failure
exception Recursive_type

let rec unify ?(weak=true) t t' =
  let var_with_numeric v t =
    assert (Typvar.def v = None);
    Typvar.restrict v;
    if not weak then Typvar.define v t
  in
  let var_with_nonnumeric v t =
    assert (Typvar.def v = None);
    if Typvar.num v then raise Unification_failure;
    if occur v t then raise Recursive_type;
    Typvar.define v t
  in
  let t, t' = deref t, deref t' in
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
  | Fun (t1, t2), Fun (t1', t2') -> unify_strong t1 t1';
                                    unify_strong t2 t2'
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
      if not weak then BatUref.unite v w
    end
  | Int, _
  | Uint, _
  | Long, _
  | Bool, _
  | Unit, _
  | Fun _, _ -> raise Unification_failure

and unify_strong t t' = unify ~weak:false t t'

module Typvars = Set.Make(Typvar)

let rec free_vars_of_typ t =
  match deref t with
  | Int | Uint | Long | Bool | Unit -> Typvars.empty
  | Fun (t1, t2) -> Typvars.union (free_vars_of_typ t1)
                                  (free_vars_of_typ t2)
  | Typvar v ->
    if Typvar.num v then Typvars.empty else Typvars.singleton v

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

type expr =
| Let of bool * string * annot option * expr
| Var of string * annot option * expr
| Ident of string
| Annot of expr * annot
| Lambda of string * annot option * expr
| Assign of expr * expr
| App of expr * expr
| Sum of expr * expr
| Eq of expr * expr
| Lt of expr * expr
| If of expr * expr * expr
| Seq of expr * expr
| Const of int
| Void

let generalizable = function Lambda _ -> true | _ -> false

(****)

(*
  let f (x : int) y (z : uint) = if x < y then x + y else x + z
*)

let test1 =
  Let (false, "f", None,
    Lambda ("x", Some Int,
    Lambda ("y", None,
    Lambda ("z", Some Uint,
      If (Lt (Ident "x", Ident "y"),
        Sum (Ident "x", Ident "y"),
        Sum (Ident "x", Ident "z"))))))

(* let f = fun x -> x *)

let test2 =
  Let (false, "f", None, Lambda ("x", None, Ident "x"))

(* let f = fun x -> x; let a = f 0; let b = f (0 = 0) *)

let test3 =
  Seq (Let (false, "f", None, Lambda ("x", None, Ident "x")),
  Seq (Let (false, "a", None, App (Ident "f", Const 0)),
       Let (false, "b", None, App (Ident "f", Eq (Const 0, Const 0)))))

(* var f = fun x -> x *)

let test4 =
  Var ("f", None, Lambda ("x", None, Ident "x"))

(* var f = fun x -> x; let a = f 0; let b = f (0 = 0) Error!*)

let test5 =
  Seq (Var ("f", None, Lambda ("x", None, Ident "x")),
  Seq (Let (false, "a", None, App (Ident "f", Const 0)),
       Let (false, "b", None, App (Ident "f", Eq (Const 0, Const 0)))))

(* 0 = (0 = 0) Error! *)

let test6 = Eq (Const 0, Eq (Const 0, Const 0))

(* fun x -> x x Error! *)

let test7 = Lambda ("x", None, App (Ident "x", Ident "x"))


(****)

type e =
| TLet of bool * string * typ * texpr
| TVar of string * typ * texpr
| TIdent of string
| TLambda of string * typ * texpr
| TAssign of texpr * texpr
| TApp of texpr * texpr
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
  | Const c -> { expr = TConst c; typ = Typvar (Typvar.fresh_num()) }, env
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
  | Lt (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    unify te1.typ te2.typ;
    { expr = TLt (te1, te2); typ = Bool }, env
  | Sum (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    let typ = Typvar (Typvar.fresh_num()) in
    unify te1.typ te2.typ;
    unify te1.typ typ;
    { expr = TSum (te1, te2); typ }, env
  | Var (id, annot, e) ->
    let te, _ = infer env e in
    begin match annot with
    | Some a -> unify_strong te.typ (typ_of_annot a)
    | None -> ()
    end;
    let schm = mono te.typ in
    let env = Env.add id schm env in
    { expr = TVar (id, te.typ, te); typ = Unit }, env
  | Let (rec_, id, annot, e) ->
    let typ =
      match annot with
      | Some a -> typ_of_annot a
      | None -> Typvar (Typvar.fresh())
    in
    let inner_env = if rec_ then Env.add id (mono typ) env else env in
    let te, _ = infer inner_env e in
    unify_strong typ te.typ;
    let schm = if generalizable e then poly env te.typ else mono te.typ in
    let env = Env.add id schm env in
    { expr = TLet (rec_, id, typ, te); typ = Unit }, env
  | Lambda (arg, annot, e) ->
    let arg_typ =
      match annot with
      | Some a -> typ_of_annot a
      | None -> Typvar (Typvar.fresh())
    in
    let inner_env = Env.add arg (mono arg_typ) env in
    let te, _ = infer inner_env e in
    { expr = TLambda (arg, arg_typ, te); typ = Fun (arg_typ, te.typ) }, env
  | App (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    let arg_typ = Typvar (Typvar.fresh()) in
    let ret_typ = Typvar (Typvar.fresh()) in
    unify_strong te1.typ (Fun (arg_typ, ret_typ));
    unify te2.typ arg_typ;
    { expr = TApp (te1, te2); typ = ret_typ }, env
  | Annot (e, annot) ->
    let te, _ = infer env e in
    unify_strong te.typ (typ_of_annot annot);
    te, env
  | If (e1, e2, e3) ->
    let te1, _ = infer env e1 in
    unify_strong te1.typ Bool;
    let te2, _ = infer env e2 in
    let te3, _ = infer env e3 in
    unify_strong te2.typ te3.typ;
    { expr = TIf (te1, te2, te3); typ = te2.typ }, env
  | Assign (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    unify te1.typ te2.typ;
    { expr = TAssign (te1, te2); typ = Unit }, env

let rec fold f v e =
  match e.expr with
  | TVoid
  | TConst _
  | TIdent _ -> f v e
  | TSeq (e1, e2)
  | TAssign (e1, e2)
  | TApp (e1, e2)
  | TEq (e1, e2)
  | TLt (e1, e2)
  | TSum (e1, e2) -> fold f (f (fold f v e1) e) e2
  | TIf (e1, e2, e3) -> fold f (fold f (fold f (f v e) e1) e2) e3
  | TVar (_, _, e1)
  | TLet (_, _, _, e1)
  | TLambda (_, _, e1) -> fold f (f v e) e1

let collect_types =
  fold (fun acc e ->
    match e.expr with
    | TLet (_, _, t, _)
    | TVar (_, t, _)
    | TLambda (_, t, _) -> t :: e.typ :: acc
    | TVoid
    | TConst _
    | TIdent _
    | TSeq _
    | TAssign _
    | TApp _
    | TEq _
    | TLt _
    | TSum _
    | TIf _ -> e.typ :: acc) []



(****)

open Printf

let rec s_typ = function
| Int -> "int"
| Uint -> "uint"
| Long -> "long"
| Bool -> "bool"
| Unit -> "unit"
| Fun (a, b) -> "(" ^ s_typ a ^ ") -> " ^ s_typ b
| Typvar v -> s_var v

and s_var v =
  match Typvar.def v with
  | None ->
    let i = string_of_int (Typvar.id v) in
    if Typvar.num v then "N" ^ i else i
  | Some t -> s_typ t

let s_set vars =
  if Typvars.cardinal vars = 0 then "" else "forall" ^
  Typvars.fold (fun v txt ->
    " " ^ string_of_int (Typvar.id v) ^ txt) vars ". "

let s_schm schm = s_set schm.qual ^ s_typ schm.shape

let p_env = Env.iter (fun id schm -> printf "%s: %s\n" id (s_schm schm))

(*
let s_texpr = function
| TVoid -> "()"
| TConst c -> string_of_int c
| TIdent id -> id
| TSeq (a, b) -> s_texpr a ^ "; " ^ s_texpr b
| TEq (a, b) -> s_texpr a ^ " = " ^ s_texpr b
| TLt (a, b) -> s_texpr a ^ " < " ^ s_texpr b
| TSum (a, b) -> s_texpr a ^ " + " ^ s_texpr b
| TVar (id, _, e) -> "var " ^ id ^ " = " ^ s_texpr e ^ ";"
*)

(****)


