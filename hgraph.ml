(* graph whose vertices are hashable *)

module type V = sig
  type t
  val equal: t -> t -> bool
  val compare: t -> t -> int
  val hash: t -> int
end

module Graph(V: V) = struct

module H = Hashtbl.Make(V)

type adj = unit H.t (* adjacency lists are actually hash tables *)
type t = { adj: adj H.t }

let create () = { adj = H.create 0 }

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
  (* 1. substitute u for v in all adjacency lists
     2. merge v's adjacency list into u's
     3. remove any u-u self-loop we might have created
     4. remove v *)
  try
    H.iter (fun x ax ->
      if H.mem ax v then (H.remove ax v; H.replace ax u ())) g.adj;
    let au = H.find g.adj u in
    iter_adj g v (fun x -> H.replace au x ());
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

