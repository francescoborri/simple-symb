open SimpleAST
module Symex = Soteria.Symex.Make (Soteria.Tiny_values.Tiny_solver.Z3_solver)
module Typed = Soteria.Tiny_values.Typed
module Compo_res = Soteria.Symex.Compo_res
module Map = Soteria.Soteria_std.Map.Make (Soteria.Soteria_std.String)
open Symex.Syntax
open Typed.Infix
open Typed.Syntax

type symb_int = Typed.T.sint Typed.t
type env = symb_int Map.t
type hist = (string * symb_int) list
type ok_state = { env : env; hist : hist }
type err_state = { msg : string; hist : hist }

let wrap_error result hist =
  let+- err_msg = result in
  { msg = err_msg; hist }

let rec symb_eval_aexpr env = function
  | Int n -> Symex.Result.ok (Typed.int n)
  | Var x -> (
      match Map.find_opt x env with
      | Some v -> Symex.Result.ok v
      | None -> Symex.Result.error (Fmt.str "Variable %s not found" x))
  | NonDet ->
      let* v = Symex.nondet Typed.t_int in
      Symex.Result.ok v
  | AOp (expr1, op, expr2) -> (
      let** v1 = symb_eval_aexpr env expr1 in
      let** v2 = symb_eval_aexpr env expr2 in
      match op with
      | Add -> Symex.Result.ok (v1 +@ v2)
      | Sub -> Symex.Result.ok (v1 -@ v2)
      | Mul -> Symex.Result.ok (v1 *@ v2)
      | Div ->
          if%sat Typed.not (v2 ==@ 0s) then
            let v2 = Typed.cast v2 in
            Symex.Result.ok (v1 /@ v2)
          else Symex.Result.error "Division by zero")

and symb_eval_bexpr env = function
  | Bool b -> Symex.Result.ok (Typed.of_bool b)
  | Not bexpr ->
      let++ v = symb_eval_bexpr env bexpr in
      Typed.not v
  | BOp (bexpr1, op, bexpr2) -> (
      let** v1 = symb_eval_bexpr env bexpr1 in
      let++ v2 = symb_eval_bexpr env bexpr2 in
      match op with And -> v1 &&@ v2 | Or -> v1 ||@ v2)
  | COp (aexpr1, op, aexpr2) -> (
      let** v1 = symb_eval_aexpr env aexpr1 in
      let++ v2 = symb_eval_aexpr env aexpr2 in
      match op with
      | Eq -> v1 ==@ v2
      | Neq -> Typed.not (v1 ==@ v2)
      | Lt -> v1 <@ v2
      | Le -> v1 <=@ v2
      | Gt -> v1 >@ v2
      | Ge -> v1 >=@ v2)

let rec symb_eval_stmt state = function
  | Skip -> Symex.Result.ok state
  | Assign (x, aexpr) ->
      let++ v = wrap_error (symb_eval_aexpr state.env aexpr) state.hist in
      { state with env = Map.add x v state.env }
  | Seq (stmt1, stmt2) ->
      let** state = symb_eval_stmt state stmt1 in
      symb_eval_stmt state stmt2
  | If (cond_bexpr, then_stmt, else_stmt) ->
      let** cond =
        wrap_error (symb_eval_bexpr state.env cond_bexpr) state.hist
      in
      if%sat cond then symb_eval_stmt state then_stmt
      else symb_eval_stmt state else_stmt
  | While (cond_bexpr, body_stmt) ->
      let** cond =
        wrap_error (symb_eval_bexpr state.env cond_bexpr) state.hist
      in
      if%sat cond then
        let** state = symb_eval_stmt state body_stmt in
        symb_eval_stmt state (While (cond_bexpr, body_stmt))
      else Symex.Result.ok state
  | Assume bexpr ->
      let** cond = wrap_error (symb_eval_bexpr state.env bexpr) state.hist in
      let* () = Symex.assume [ cond ] in
      Symex.Result.ok state
  | Assert bexpr ->
      let** cond = wrap_error (symb_eval_bexpr state.env bexpr) state.hist in
      (* In OX mode, result = true iff not cond is UNSAT *)
      let* result = Symex.assert_ cond in
      if result then Symex.Result.ok state
      else
        Symex.Result.error
          {
            msg = Fmt.str "Assertion %a failed" Typed.ppa cond;
            hist = state.hist;
          }
  | Invoke (f, arg_aexpr) ->
      let++ arg = wrap_error (symb_eval_aexpr state.env arg_aexpr) state.hist in
      { state with hist = (f, arg) :: state.hist }
  | AssignInvoke (x, f, arg_aexpr) ->
      let** arg = wrap_error (symb_eval_aexpr state.env arg_aexpr) state.hist in
      symb_eval_stmt
        { state with hist = (f, arg) :: state.hist }
        (Assign (x, NonDet))

let build_symb_process stmt =
  let result =
    let++ { env; hist } = symb_eval_stmt { env = Map.empty; hist = [] } stmt in
    { env; hist = List.rev hist }
  in
  let result =
    let+- { msg; hist } = result in
    { msg; hist = List.rev hist }
  in
  result
