open SimpleAST
open SimpleSymbInterpreter

let build_indent_string level = String.make level ' '
let next_indent_level indent_level = indent_level + 4

let empty_or_add_newline str =
  if String.equal str String.empty then " ()" else "\n" ^ str

let string_of_env ~indent_level env =
  let indent = build_indent_string indent_level in
  env |> Map.bindings
  |> List.map (fun (x, v) -> Fmt.str "%s%s -> %a" indent x Typed.ppa v)
  |> String.concat "\n"

let string_of_hist ~indent_level hist =
  let indent = build_indent_string indent_level in
  hist
  |> List.mapi (fun idx (f, arg) ->
      Fmt.str "%s- Call#%d: %s(%a)" indent (idx + 1) f Typed.ppa arg)
  |> String.concat "\n"

let string_of_path_condition ~indent_level path_condition =
  let indent = build_indent_string indent_level in
  path_condition
  |> List.map (Fmt.str "%s%a" indent Symex.Value.ppa)
  |> String.concat " /\\\n"

let string_of_state idx (result, path_condition) =
  let indent_level1 = next_indent_level 0 in
  let indent_level2 = next_indent_level indent_level1 in
  let indent_string1 = build_indent_string indent_level1 in
  let path_condition_str =
    path_condition
    |> string_of_path_condition ~indent_level:indent_level2
    |> empty_or_add_newline
  in
  match Soteria.Symex.Compo_res.to_result_opt result with
  | Some (Ok { env; hist }) ->
      Fmt.str
        "Symbolic execution result %d:\n\
         %sSUCCESS\n\
         %sPath condition:%s\n\
         %sEnvironment:%s\n\
         %sCall history:%s"
        idx indent_string1 indent_string1 path_condition_str indent_string1
        (string_of_env ~indent_level:indent_level2 env |> empty_or_add_newline)
        indent_string1
        (string_of_hist ~indent_level:indent_level2 hist |> empty_or_add_newline)
  | Some (Error { msg; hist }) ->
      Fmt.str
        "Symbolic execution result %d:\n\
         %sERROR: %s\n\
         %sPath condition:%s\n\
         %sCall history:%s"
        idx indent_string1 msg indent_string1 path_condition_str indent_string1
        (string_of_hist ~indent_level:indent_level2 hist |> empty_or_add_newline)
  | None ->
      Fmt.str
        "Symbolic execution result %d:\n%sPath condition: %s\n%sResult: Unknown"
        idx indent_string1 path_condition_str indent_string1
