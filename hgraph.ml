(* graph whose vertices are hashable *)

module type V = sig
  type t
  val equal: t -> t -> bool
  val compare: t -> t -> int
  val hash: t -> int
end

module Undirected(V: V) = struct

module H = Hashtbl.Make(V)

type adj = unit H.t (* adjacency lists are actually hash tables *)
type t = { adj: adj H.t }

let create n = { adj = H.create n }

let clear g = H.clear g.adj

let add_vertex g v =
  if not (H.mem g.adj v) then
    H.add g.adj v (H.create 0)

let add_edge g u v = (* idempotent *)
  if not (V.equal u v) then
    try
      let au = H.find g.adj u in
      let av = H.find g.adj v in
      H.replace au v ();
      H.replace av u ()
    with
    Not_found -> ()

let rm_edge g u v =
  try
    let au = H.find g.adj u in
    let av = H.find g.adj v in
    H.remove au v;
    H.remove av u
  with
  Not_found -> ()

let iter_adj g v f =
  try
    let av = H.find g.adj v in
    H.iter (fun v () -> f v) av
  with
  Not_found -> ()

let adj_list g v =
  try
    let av = H.find g.adj v in
    H.fold (fun x () lst -> x :: lst) av []
  with
  Not_found -> []

let rm_vertex g v =
  iter_adj g v (fun x -> let ax = H.find g.adj x in H.remove ax v);
  H.remove g.adj v

let merge_vertices g u v =
  (* 1. substitute u for v in adjacency lists of all v's neighbors
     2. (at the same time) merge v's adjacency list into u's
     3. remove any u-u self-loop we might have created
     4. remove v *)
  if not (V.equal u v) then
    try
      let au = H.find g.adj u in
      iter_adj g v (fun x ->
        let ax = H.find g.adj x in
        H.remove ax v;
        H.replace ax u ();
        H.replace au x ());
      H.remove au u;
      H.remove g.adj v
    with
    Not_found -> ()

module VSet = Set.Make(V)

let iter_ccs g f =
  let seeds = H.fold (fun v _ set -> VSet.add v set) g.adj VSet.empty in
  let seen = H.create 0 in
  let rec bfs frontier cc =
    if VSet.is_empty frontier then cc else begin
      VSet.iter (fun v -> H.add seen v ()) frontier;
      let frontier, cc = VSet.fold (fun v (s, cc) ->
        let disc = List.filter (fun x -> not (H.mem seen x)) (adj_list g v) in
        (List.fold_right VSet.add disc s, v :: cc))
          frontier (VSet.empty, cc) in
      bfs frontier cc
    end
  in
  let rec loop seeds =
    if VSet.is_empty seeds then () else begin
      let v = VSet.choose seeds in
      let cc = bfs (VSet.singleton v) [] in
      f cc;
      let seeds = List.fold_right VSet.remove cc seeds in
      loop seeds
    end
  in
  loop seeds

end

module Directed(V: V) = struct

module H = Hashtbl.Make(V)

type adj = unit H.t
type t = { pred: adj H.t; succ: adj H.t }

let create n = { pred = H.create n; succ = H.create n }

let clear g = H.clear g.pred; H.clear g.succ

let add_vertex g v =
  if not (H.mem g.pred v) then begin
    H.add g.pred v (H.create 0);
    H.add g.succ v (H.create 0)
  end

let add_edge g u v =
  try
    let su = H.find g.succ u in
    let pv = H.find g.pred v in
    H.replace su v ();
    H.replace pv u ()
  with
  Not_found -> ()

let iter_pred g v f =
  try
    let pv = H.find g.pred v in
    H.iter (fun u () -> f u) pv
  with
  Not_found -> ()

let fold_pred g v f x =
  try
    let pv = H.find g.pred v in
    H.fold (fun u () x -> f u x) pv x
  with
  Not_found -> x

let iter_succ g v f =
  try
    let sv = H.find g.succ v in
    H.iter (fun u () -> f u) sv
  with
  Not_found -> ()

let merge_vertices g u v =
  (* 1. substitute u for v in successors list of each of v's predecessors
     2. (at the same time) add each predecessor of v to u's predecessors
     3. substitute u for v in pred. list of each of v's successors
     4. (at the same time) add each successor of v to u's successors
     5. remove v
   *)
  if not (V.equal u v) then try
    let pu = H.find g.pred u in
    let su = H.find g.succ u in
    iter_pred g v (fun x ->
      let sx = H.find g.succ x in
      H.remove sx v;
      H.replace sx u ();
      H.replace pu x ());
    iter_succ g v (fun x ->
      let px = H.find g.pred x in
      H.remove px v;
      H.replace px u ();
      H.replace su x ());
    H.remove g.pred v;
    H.remove g.succ v
  with
  Not_found -> ()

let induced g vs =
  let n = List.length vs in
  let s = { pred = H.create n; succ = H.create n } in
  List.iter (fun v -> H.add s.pred v (H.create 10);
                      H.add s.succ v (H.create 10)) vs;
  List.iter (fun v ->
    let pg = H.find g.pred v in
    let sg = H.find g.succ v in
    let pv = H.find s.pred v in
    let sv = H.find s.succ v in
    H.iter (fun p () -> if H.mem s.pred p then H.add pv p ()) pg;
    H.iter (fun p () -> if H.mem s.pred p then H.add sv p ()) sg) vs;
  s

type g = t

module G = struct
  type t = g
  module V = V
  let iter_vertex f g = H.iter (fun v _ -> f v) g.pred
  let iter_succ f g v = iter_succ g v f
  let in_degree g v = H.length (H.find g.pred v)
end
module Comp = Graph.Components.Make(G)
module Topo = Graph.Topological.Make(G)

let scc_array g =
  let a = Comp.scc_array g in
  let topo scc =
    let subg = induced g scc in
    List.rev (Topo.fold (fun v lst -> v :: lst) subg [])
  in
  Array.iteri (fun i scc -> a.(i) <- topo scc) a;
  a

end

