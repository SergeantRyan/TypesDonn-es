open Graphstruct
open Lang
open Instr
 
type environment = { types:  db_tp; bindings: (vname * label) list }

let initial_environment gt = {types = gt; bindings = []}
let initial_result gt = Result.Ok (initial_environment gt)
  
exception FieldAccError of string
exception TypeError of string


type tc_result = (environment, string list) result

(* Functions for manipulating the environment *)

let add_var vn t (env:environment) = 
  {env with bindings = (vn,t)::env.bindings}

let remove_var vn env = 
  {env with bindings = List.remove_assoc vn env.bindings}

(*let check_graph_types (DBG (ntdecls, rtdelcs)) =
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
  if errors = [] then Result.Ok () else Result.Error errors*)

  let check_graph_types (DBG (ntdecls, rtdecls)) = Result.Ok ()

(*let rec tp_expr env expr =
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
        | Some t -> Result.Ok t*)

let rec tp_expr env = function
  Const v -> IntT
| AttribAcc (vn, fn) -> IntT
| BinOp (bop, e1, e2) -> tp_expr env e1

let check_expr e et env : tc_result = 
  try 
    if tp_expr env e = et
    then Result.Ok env
    else Result.Error ["Expression does not have expected type " ^ (show_attrib_tp et)]
  with 
  | TypeError s -> Result.Error [s]
  | FieldAccError s -> Result.Error [s]
  

let tc_instr (i: instruction) (env: environment) : tc_result = 
  match i with
  | IActOnNode (_act, vn, lb) -> Result.Error ["not yet implemented"]
  | _  -> Result.Error ["also not implemented"]

(* type check list of instructions and stop on error *)
let check_and_stop (res : tc_result) i : tc_result = Result.bind res (tc_instr i)

let tc_instrs_stop gt instrs : tc_result = 
  List.fold_left check_and_stop (initial_result gt) instrs

  (* TODO: typecheck instructions *)
let typecheck_instructions continue gt instrs np = 
  let r = Result.Ok initial_environment in   (* call to real typechecker here *)
  match r with
  | Result.Error etc -> Printf.printf "%s\n" (String.concat "\n" etc); 
                        failwith "stopped"
  |_ -> np
  

  (* Typecheck program; 
     If continue is true, continue typechecking even 
     when errors have been discovered (can be ignored in a first version) *)  
let typecheck continue (NormProg(gt, NormQuery instrs) as np) = 
  match check_graph_types gt with
  | Result.Error egt -> Printf.printf "%s\n" ("Undeclared types in\n" ^ egt);
                        failwith "stopped"
  | _ -> typecheck_instructions continue gt instrs np
