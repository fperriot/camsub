open Tools

type 'a typp = Int | Uint | Long | Bool | Unit | Fun of 'a typp * 'a typp
  | Typvar of 'a

type kind = Any | Num | Iso

type core = { id: int; mutable def: typ option }
and typvar = core BatUref.t
and dualvar = {
  kind: kind BatUref.t;
  numvar: typvar;
  isovar: typvar;
}
and typ = dualvar typp

let kind v = BatUref.uget v.kind

let id v = (BatUref.uget v).id
let def v = (BatUref.uget v).def
let define v t = (BatUref.uget v).def <- Some t

let eitherdef v =
  match kind v with
  | Any -> None
  | Num -> def v.numvar
  | Iso -> def v.isovar

let isodef v =
  match kind v with
  | Any -> None
  | Num -> None
  | Iso -> def v.isovar

let counter = ref 0

let uid() = let c = !counter in incr counter; c

let uid_pair() =
  let c = !counter in
  incr counter;
  incr counter;
  c, c+1

(* Note: it's important to dereference definitions of isolated-type variables
   but not of numeric-type variables, because it allows for weak unification
   of numeric-type variables even though some of them may already be defined
 *)

let deref = function
  | Typvar v -> (match isodef v with Some t -> t | None -> Typvar v)
  | t -> t

module Typvar = struct
  type t = typvar
  let equal a b = (id a = id b)
  let compare a b = compare (id a) (id b)
  let hash a = id a
end

module G = Hgraph.Undirected(Typvar)

let g = G.create 0

let fresh_var ?(kind=Any) () =
  let id = uid() in
  let numvar = BatUref.uref { id; def = None } in
  G.add_vertex g numvar;
  Printf.printf "Adding vertex %d\n" id;
  { kind = BatUref.uref kind;
    numvar;
    isovar = BatUref.uref { id; def = None } }

let fresh_num() = fresh_var ~kind:Num ()

module VH = Hashtbl.Make(Typvar)

let rec occur v t =
  match deref t with
  | Int | Uint | Long | Bool | Unit -> false
  | Fun (t1, t2) -> occur v t1 || occur v t2
  | Typvar v' -> Typvar.equal v v'.isovar

exception Unification_failure
exception Recursive_type

let rec unify ?(weak=true) t t' =
  let var_with_numeric v t =
    begin match kind v with
    | Any -> BatUref.uset v.kind Num
    | Num -> ()
    | Iso -> raise Unification_failure
    end;
    if not weak then begin
      match def v.numvar with
      | None -> define v.numvar t (* TODO decommission sibling isovar *)
      | Some t' -> if t <> t' then raise Unification_failure
    end
  in
  let var_with_nonnumeric v t =
    if occur v.isovar t then raise Recursive_type;
    begin match kind v with
    | Any -> BatUref.uset v.kind Iso
    | Num -> raise Unification_failure
    | Iso -> assert false
    end;
    assert (def v.isovar = None);
    define v.isovar t (* TODO decommission sibling numvar *)
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
  | Typvar v, Typvar v' ->
    let sel k1 k2 =
      match k1, k2 with
      | Any, Any -> Any
      | Any, Num
      | Num, Any
      | Num, Num -> Num
      | Any, Iso
      | Iso, Any
      | Iso, Iso -> assert false
      | Num, Iso
      | Iso, Num -> raise Unification_failure
    in
    BatUref.unite ~sel v.kind v'.kind;
    BatUref.unite v.isovar v'.isovar;
    if weak then begin
      Printf.printf "Creating edge %d-%d\n" (id v.numvar) (id v'.numvar);
      G.add_edge g v.numvar v'.numvar
    end else begin
      Printf.printf "Merging %d and %d\n" (id v.numvar) (id v'.numvar);
      G.merge_vertices g v.numvar v'.numvar;
      let sel n1 n2 =
        let def =
          match n1.def, n2.def with
          | None, None -> None
          | None, Some x
          | Some x, None -> Some x
          | Some x, Some y ->
            if x = y then Some x else raise Unification_failure
        in
        { id = n1.id; def }
      in
      BatUref.unite ~sel v.numvar v'.numvar
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
    if kind v = Any then Typvars.singleton v.isovar else Typvars.empty

type scheme = {
  qual: Typvars.t;    (* Universally qualified type variables *)
  shape: typ
}

let free_vars_of_scheme s = Typvars.diff (free_vars_of_typ s.shape) s.qual

(* instantiate a type scheme by replacing all universally qualified type
   variables occuring in the scheme with fresh type vars *)

let instance schm =
  let n = Typvars.cardinal schm.qual in
  let h = VH.create n in
  Typvars.iter (fun v -> VH.add h v (fresh_var())) schm.qual;
  let rec inst t =
    let t = deref t in
    match t with
    | Int | Uint | Long | Bool | Unit -> t
    | Fun (t1, t2) -> Fun (inst t1, inst t2)
    | Typvar v -> Typvar (try VH.find h v.isovar with Not_found -> v)
  in
  inst schm.shape

type annot = int typp

let typ_of_annot a =
  let h = Hashtbl.create 0 in
  let v i =
    try Hashtbl.find h i with Not_found ->
      let v = fresh_var() in
      Hashtbl.add h i v; v
  in
  let rec f = function
  | Int -> Int
  | Uint -> Uint
  | Long -> Long
(*
  | Int -> Typvar (fresh_num ~typ:Int ())
  | Uint -> Typvar (fresh_num ~typ:Uint ())
  | Long -> Typvar (fresh_num ~typ:Long ())
*)
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

(* let m = fun x -> fun y -> if x < y then 0 else 1 *)

let test8 =
  Let (false, "m", None,
    Lambda ("x", None,
    Lambda ("y", None,
      If (Lt (Ident "x", Ident "y"), Const 0, Const 1))))

(* let m = fun x -> fun y -> if x < y then (x:int) else 1 *)

let test9 =
  Let (false, "m", None,
    Lambda ("x", None,
    Lambda ("y", None,
      If (Lt (Ident "x", Ident "y"),
        Annot (Ident "x", Int),
        Const 1))))

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
  | Const c -> { expr = TConst c; typ = Typvar (fresh_num()) }, env
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
    let typ = Typvar (fresh_num()) in
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
    let typ = Typvar (fresh_var()) in
    begin match annot with
    | Some a -> unify_strong typ (typ_of_annot a)
    | None -> ()
    end;
    let inner_env = if rec_ then Env.add id (mono typ) env else env in
    let te, _ = infer inner_env e in
    unify_strong typ te.typ;
    let schm = if generalizable e then poly env te.typ else mono te.typ in
    let env = Env.add id schm env in
    { expr = TLet (rec_, id, typ, te); typ = Unit }, env
  | Lambda (arg, annot, e) ->
    let arg_typ = Typvar (fresh_var()) in
    begin match annot with
      | Some a -> unify_strong arg_typ (typ_of_annot a)
      | None -> ()
    end;
    let inner_env = Env.add arg (mono arg_typ) env in
    let te, _ = infer inner_env e in
    { expr = TLambda (arg, arg_typ, te); typ = Fun (arg_typ, te.typ) }, env
  | App (e1, e2) ->
    let te1, _ = infer env e1 in
    let te2, _ = infer env e2 in
    let arg_typ = Typvar (fresh_var()) in
    let ret_typ = Typvar (fresh_var()) in
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
  match eitherdef v with
  | None ->
    begin match kind v with
    | Any -> "N" ^ string_of_int (id v.numvar) ^ "," ^ string_of_int (id v.isovar)
    | Num -> "N" ^ string_of_int (id v.numvar)
    | Iso -> string_of_int (id v.isovar)
    end
  | Some t -> s_typ t

let s_set vars =
  if Typvars.cardinal vars = 0 then "" else "forall" ^
  Typvars.fold (fun v txt ->
    " " ^ string_of_int (id v) ^ txt) vars ". "

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

let refine () =
  G.iter_ccs g (fun vars ->
    printf "CC:";
    List.iter (fun v -> printf " %d" (id v)) vars;
    printf "\n";
    let defs = filter_revmap def vars in
    match defs with
    | [] -> List.iter (fun v -> define v Int) vars
    | d :: defs ->
      if List.for_all (( = ) d) defs then
        List.iter (fun v -> define v d) vars)


