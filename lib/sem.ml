(* Semantics of instructions *)
open Lang
open Graphstruct
open Instr


  (* State of the program, essentially a graph structure and a binding in form of a table,
  and as convenience info an overapproximation of the maximal node number
  allocated in the graph (could in principle be recomputed each time)
  Nodes have a unique identifier (an int) which is incremented when creating new nodes.
  When deleting nodes, the max node number is currently not decremented, 
  thus does not reflect the number of nodes in the graph, but one could think
  of a garbage collector when running out of node identifiers.
   *)

(* Naive implementation of bindings as tables, ie. 
   a heading (variable list 'v list) and a list of lines containing nodes 
   that each have the same length as the variable list  *)

type ('v, 'n) table = Table of 'v list * 'n list list
  [@@deriving show]

type vname_nodeid_table = (vname, nodeid) table
  [@@deriving show]

let empty_table = Table([], [[]])

(* Add a single variable v, bound to a single node n, to a table,
  as during node creation (old interpretation, now superseded, 
  see create_node and add_var_mult_nodes_to_table) *)
let add_var_single_node_to_table v n (Table (vns, lns)) = 
    Table (v::vns, List.map (fun ln -> n::ln) lns)

(* Add multiple nodes contained in ns for a new variable v to a table,
  one node per line. ns and lns have to have the same length.  *)
let add_var_mult_nodes_to_table v ns (Table (vns, lns)) = 
      Table (v::vns, List.map2 (fun n ln -> n::ln) ns lns)
      


type attrib_val = fieldname * value
  [@@deriving show]
type attrib_struct = label * (attrib_val list)
  [@@deriving show]
      
type db_graph_struct = (Graphstruct.nodeid, attrib_struct, label) Graphstruct.db_graph
  [@@deriving show]
 

type state = State of db_graph_struct * (vname, nodeid) table * nodeid
let initial_state = State(empty_graph, empty_table, 0)

let create_node v lb (State(g, tab, mn)) = 
  let Table(_vns, lns) = tab in 
  let new_node_ids = List.init (List.length lns) (fun i -> mn +i) in 
  let new_nodes = List.init (List.length lns) (fun i -> DBN(mn + i , (lb, []))) in
  let new_tab = add_var_mult_nodes_to_table v new_node_ids tab in
  let new_graph = add_nodes_to_graph new_nodes g in 
  State (new_graph, new_tab, mn + 1)

let create_rel sv lb tv (State(g, tab, mn)) = 
  let Table(vns, lns) = tab in 
  let nid1= List.nth (List.hd lns) (Option.get (List.find_index (fun v -> v==sv) vns)) in 
  let nid2= List.nth (List.hd lns) (Option.get (List.find_index (fun v -> v==tv) vns)) in
  let r= DBR(nid1,lb,nid2) in
  let new_graph = add_rel_to_graph g r in 
  State (new_graph, tab, mn) 

let match_node v lb (State(g, tab, mn)) = 
  let Table(_vns, lns) = tab in 
  let new_node_ids = List.init (List.length lns) (fun i -> i) in (*probablement faux*) 
  let new_tab = add_var_mult_nodes_to_table v new_node_ids tab in
  State (g, new_tab, mn)

let match_rel sv lb tv (State(g, tab, mn)) = 
  State (g, tab, mn)  (*dépend de match node incomplet*)

(*let delete vs (State(g, tab, mn))=
let Table(_vns, lns) = tab in 
let new_tab =  in
let new_graph = List.filter (fun gr -> source_of_rel(rels_of_graph(g))!= v && target_of_rel(rels_of_graph(g))!=v) in 
State (new_graph, new_tab, mn + 1)*)

(* TODO: complete following definition *)
let exec_instr s = function
  | IActOnNode (CreateAct, v, lb) -> create_node v lb s 
  | IActOnRel (CreateAct,sv,lb,tv) -> create_rel sv lb tv s 
  | IActOnNode (MatchAct, v, lb) -> match_node v lb s 
  | IActOnRel (MatchAct,sv,lb,tv) -> match_rel sv lb tv s
  (**| IDeleteNode (vs) -> 
  | IDeleteRel -> 
  | IReturn ->
  | IWhere ->
  | ISet ->*) 
  | _ -> s
  

let exec (NormProg(_tps, NormQuery(instrs))) = 
  List.fold_left exec_instr initial_state instrs

