(* Normalized language, after removal of patterns and other syntactic sugar *)

open Lang

type action = CreateAct | MatchAct
  [@@deriving show]

type instruction
  = IActOnNode of action * vname * label
  | IActOnRel of action * vname * label * vname
  | IDeleteNode of vname
  | IDeleteRel of vname * label * vname 
  | IReturn of vname list
  | IWhere of expr
  | ISet of vname * fieldname * expr 
  [@@deriving show]

(* Normalized query *)
type norm_query = NormQuery of instruction list
  [@@deriving show]

type norm_prog = NormProg of db_tp * norm_query
  [@@deriving show]

let normalize_node_pattern act = function 
  | DeclPattern (v, l) -> (v, [IActOnNode(act, v, l)])
  | VarRefPattern (v) -> (v, [])

let rec normalize_pattern act = function 
  | SimpPattern p -> normalize_node_pattern act p
  | CompPattern (np1, rlab, p2) ->
      let (v1, insts1) = normalize_node_pattern act np1 in
      let (v2, insts2) = normalize_pattern act p2 in
      (v1, insts1 @ insts2 @ [IActOnRel(act, v1, rlab, v2)])

let normalize_clause = function
  | Create pats -> 
      List.concat_map (fun p -> snd (normalize_pattern CreateAct p)) pats
  | Match pats -> 
      List.concat_map (fun p -> snd (normalize_pattern MatchAct p)) pats
  | Delete (DeleteNodes vs) ->
      List.map (fun v -> IDeleteNode v) vs
  | Delete (DeleteRels rels) ->
      List.map (fun (v1, r, v2) -> IDeleteRel (v1, r, v2)) rels
  | Return vs -> [IReturn vs]
  | Where e -> [IWhere e]
  | Set lst -> List.map (fun (v, f, e) -> ISet (v, f, e)) lst

let normalize_query (Query cls) =
  NormQuery (List.concat_map normalize_clause cls)

let normalize_prog (Prog (tds, q)) =
  NormProg (tds, normalize_query q)
