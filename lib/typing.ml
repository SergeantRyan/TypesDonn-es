open Lang
open Graphstruct

(* Environnement de typage *)
type environment = {
  types : db_tp;
  bindings : (vname * label) list;
}

type tc_result = (environment, string list) result

let add_var vn lb env =
  { env with bindings = (vn, lb) :: env.bindings }

let remove_var vn env =
  { env with bindings = List.remove_assoc vn env.bindings }

let check_graph_types (DBG (ntdecls, rtdelcs)) =
  let node_labels = List.map (fun { nlabel; _ } -> nlabel) ntdecls in
  let errors =
    List.fold_left (fun acc { rlabel; rstart; rend; _ } ->
      let errs = [] in
      let errs = if not (List.mem rstart node_labels) then
        ("Start node type of relation '" ^ rlabel ^ "' does not exist: " ^ rstart) :: errs else errs in
      let errs = if not (List.mem rend node_labels) then
        ("End node type of relation '" ^ rlabel ^ "' does not exist: " ^ rend) :: errs else errs in
      acc @ errs
    ) [] rtdelcs
  in
  if errors = [] then Result.Ok () else Result.Error errors

let rec tp_expr env expr =
  match expr with
  | Bool b -> Result.Ok BoolT
  | Int _ -> Result.Ok IntT
  | String _ -> Result.Ok StringT
  | Binop (e1, _, e2) ->
    tp_expr env e1 >>= fun t1 ->
    tp_expr env e2 >>= fun t2 ->
    if t1 = t2 then Result.Ok t1
    else Result.Error ["Type mismatch in binary operation"]
  | Access (v, field) ->
    match List.assoc_opt v env.bindings with
    | None -> Result.Error ["Variable not found: " ^ v]
    | Some label ->
      let DBG (nodes, _) = env.types in
      match List.find_opt (fun { nlabel; _ } -> nlabel = label) nodes with
      | None -> Result.Error ["Unknown label for variable: " ^ v]
      | Some { nattribs; _ } ->
        match List.assoc_opt field nattribs with
        | None -> Result.Error ["Field not found: " ^ field ^ " in node type " ^ label]
        | Some t -> Result.Ok t

let check_expr e expected env =
  tp_expr env e >>= fun actual ->
  if actual = expected then Result.Ok env
  else Result.Error ["Expression does not have expected type"]

let tc_instr (i : instruction) (env : environment) : tc_result =
  let DBG (nodes, _) = env.types in
  let label_exists lb =
    List.exists (fun { nlabel; _ } -> nlabel = lb) nodes
  in
  match i with
  | IActOnNode (_act, vn, lb) ->
      if List.mem_assoc vn env.bindings then
        Result.Error ["Variable already declared: " ^ vn]
      else if not (label_exists lb) then
        Result.Error ["Label does not exist: " ^ lb]
      else
        Result.Ok (add_var vn lb env)

  | IActOnRel (_act, v1, _lb, v2) ->
      let undeclared = List.filter (fun v -> not (List.mem_assoc v env.bindings)) [v1; v2] in
      if undeclared = [] then Result.Ok env
      else Result.Error ["Undeclared variables in relation: " ^ String.concat ", " undeclared]

  | IDeleteNode vn ->
      if List.mem_assoc vn env.bindings then
        Result.Ok (remove_var vn env)
      else
        Result.Error ["Variable not found for deletion: " ^ vn]

  | IDeleteRel (v1, _lb, v2) ->
      let undeclared = List.filter (fun v -> not (List.mem_assoc v env.bindings)) [v1; v2] in
      if undeclared = [] then Result.Ok env
      else Result.Error ["Undeclared variables in relation deletion: " ^ String.concat ", " undeclared]

  | IReturn vs ->
      let duplicate v l = List.length (List.filter ((=) v) l) > 1 in
      if List.exists (fun v -> not (List.mem_assoc v env.bindings)) vs then
        Result.Error ["Undeclared variable(s) in return"]
      else if List.exists (fun v -> duplicate v vs) vs then
        Result.Error ["Duplicate variable(s) in return"]
      else
        let filtered = List.filter (fun (v, _) -> List.mem v vs) env.bindings in
        Result.Ok { env with bindings = filtered }

  | IWhere e ->
      check_expr e BoolT env

  | ISet (v, f, e) ->
      if not (List.mem_assoc v env.bindings) then
        Result.Error ["Undeclared variable in Set: " ^ v]
      else
        let label = List.assoc v env.bindings in
        let node = List.find (fun { nlabel; _ } -> nlabel = label) nodes in
        match List.assoc_opt f node.nattribs with
        | None -> Result.Error ["Field " ^ f ^ " not found in node type " ^ label]
        | Some tp -> check_expr e tp env

let typecheck (NormProg (db, instrs)) =
  match check_graph_types db with
  | Result.Error errs -> Result.Error errs
  | Result.Ok () ->
      let env0 = { types = db; bindings = [] } in
      let rec loop instrs env acc_errors =
        match instrs with
        | [] -> if acc_errors = [] then Result.Ok env else Result.Error acc_errors
        | i :: rest ->
            match tc_instr i env with
            | Result.Ok env' -> loop rest env' acc_errors
            | Result.Error errs -> loop rest env (acc_errors @ errs)
      in
      loop instrs env0 []
