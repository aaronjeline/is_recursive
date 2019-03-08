open Core_kernel.Std
open Bap.Std
open Graphlib.Std
open Format
include Self()

module CG = Graphs.Callgraph


type proof = Direct of tid | Mutual of tid list

let proofeq a b = match (a,b) with
  | (Direct a, Direct b) -> a = b
  | _ -> false

(* Break an edge into a tuple containing the label of its src/dst*)
let breakedge e = (CG.Node.label @@ CG.Edge.src e, CG.Node.label @@ CG.Edge.dst e)

let name2tid prog name =
  Term.enum sub_t prog |>
  Seq.find_map ~f:(fun s -> Option.some_if (Sub.name s = name) (Term.tid s))

let tid2name prog tid =
  let res =
    Term.enum sub_t prog |>
    Seq.find_map ~f:(fun s -> Option.some_if (Term.tid s = tid) (Sub.name s))
  in match res with
  | None -> raise (Failure "Test")
  | Some s -> s

let rec consume s = match Seq.next s with
  | None -> []
  | Some (x,xs) -> x::(consume xs)

let path2list p: tid list = Seq.map (Path.edges p)
    (fun e -> let (src,dst) = breakedge e in src)
    |> consume




(* Pull the children of passed tid*)
let children cg tid =
  Seq.filter_map
    (CG.edges cg)
    (fun e -> let (src,dst) = breakedge e in
      if tid = src then Some dst else None)


(* Collect all subroutines in the program*)
let find_subs prog = Term.enum sub_t prog

let print_subs subs =
  let print_sub s = printf "%s\n" (Sub.name s) in
  Seq.iter subs print_sub

let print_proof prog p =
  match p with
  | Direct tid -> printf "%s is directly recursive\n" (tid2name prog tid)
  | Mutual path ->
    List.iter
      path
      (fun tid -> printf " -> %s" (tid2name prog tid));
    printf "\n"

(* Find cases of direct recursion *)
let prove_direct prog cg tid: proof option =
  let prover id = if id = tid then Some (Direct tid) else None in
  Seq.find_map (children cg tid) prover

let prove_mutual prog cg tid: proof option =
  let prover id = Graphlib.shortest_path (module CG) cg id tid in
  let unwrapper p = Mutual ((tid::(path2list p)) @ [tid]) in
  Option.map (Seq.find_map (children cg tid) prover) unwrapper

let main proj =
  let prog = Project.program proj in
  let cg = Program.to_graph prog in
  let subs = Seq.map (find_subs prog) Term.tid in
  let drec = consume (Seq.filter_map subs (prove_direct prog cg)) in
  printf "Directly Recursive Functions:\n";
  List.iter
    drec
    (print_proof prog);
  printf "Mutually Recursive Functions:\n";
  Seq.iter
    (Seq.filter_map subs (fun tid -> if List.mem drec (Direct tid) proofeq then None else (prove_mutual prog cg tid)))
    (print_proof prog)




module Cmdline = struct
  open Config

  let () = when_ready (fun{get=(!!)} ->
      Project.register_pass' (main))

  let () = manpage [
      `S "Description";
      `P
      "Checks For Recursive Functions"
    ]
end

