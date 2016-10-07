(* To compile this file, run:
 *
 * ocamlbuild -use-ocamlfind -pkg compsci631 -pkg ppx_test interp.d.byte
 *
 * This produces an executable called interp.d.byte.
 *
 * You can use write inline unit tests using the same technique you used
 * in the last assignment.
 *)
module PTest = Ppx_test.Test
open Interp_util
open Printf

let to_int (e: exp) :  int = 
  match e with 
  | Const (Int n) -> n
  | _ -> failwith  "expected int"

let to_bool (e: exp): bool = 
  match e with 
  | Const (Bool b) -> b
  | _ -> failwith "expected bool"

let rec to_list (e: exp): 'a list = 
  match e with
  | Empty -> []
  | Cons (hd, tl) -> hd :: to_list tl
  | _ -> failwith "expected a list"

let to_record (e: exp): (string * exp) list = 
  match e with
  | Record e -> e
  | _ -> failwith "expected a record"

let is_empty (e: exp): exp =
  (*
  let li = to_list e in
  Const (Bool (List.length li = 0))
  *)
  match e with 
  | Empty -> Const (Bool true)
  | Cons (hd, tl) -> Const (Bool false)
  | _ -> failwith "expected a list"

let extract_head (e: exp): exp =
 (*
  let li = to_list e in 
  match li with 
  | [] -> failwith "cannot extract head of empty list"
  | hd :: tl -> hd
 *)
  match e with
  | Empty -> failwith "cannot extract head of empty list"
  | Cons (hd, tl) -> hd
  | _ -> failwith "expected a list"

let extract_tail (e: exp): exp =
  match e with
  | Empty -> failwith "cannot extract tail of empty list"
  | Cons (hd, tl) -> tl
  | _ -> failwith "expected a list"

let rec subst (x: id) (v: exp) (e: exp): exp =
  match e with
  | Const c ->  Const c
  | Op2 (op, e1, e2) -> Op2 (op, subst x v e1, subst x v e2)
  | If (e1, e2, e3) -> If (subst x v e1, subst x v e2, subst x v e3)
  | Let (y, e1, e2) ->
  Let (y, subst x v e1 , if x = y then e2 else subst x v e2)
  | Cons (hd, tl) -> Cons (subst x v hd, subst x v tl)
  | Head e -> Head (subst x v e)
  | Tail e -> Tail (subst x v e)
  | IsEmpty e -> IsEmpty (subst x v e)
  | Empty -> Empty
  | Record e -> Record (List.map (fun (key, value) -> (key, subst x v value)) e)
  | GetField (r, f) ->  GetField (subst x v r, f)
  | App (fn, arg) -> App (subst x v fn, subst x v arg)
  | Fun (param, body) -> if x = param then Fun (param, body) else Fun (param, subst x v body)
  | Fix (name, body) -> Fix (name, subst name (Fix (name, body)) body)
  | Id y -> if x = y then v else Id y
  | _ -> failwith "we don't know how to substitute for this yet! get cracking."

let rec eval (e: exp) : exp =
  let _ = pp_exp Format.std_formatter e in
  let _ = printf "\n\n" in
  match e with
  | Const c ->  Const c
  | Op2 (LT, e1, e2) -> Const (Bool (to_int (eval e1) < to_int (eval e2)))
  | Op2 (GT, e1, e2) -> Const (Bool (to_int (eval e1) > to_int (eval e2)))
  | Op2 (Eq, e1, e2) -> Const (Bool (to_int (eval e1) = to_int (eval e2)))
  | Op2 (Add, e1, e2) -> Const (Int (to_int (eval e1) + to_int (eval e2)))
  | Op2 (Sub, e1, e2) -> Const (Int (to_int (eval e1) - to_int (eval e2)))
  | Op2 (Mul, e1, e2) -> Const (Int (to_int (eval e1) * to_int (eval e2)))
  | Op2 (Div, e1, e2) -> Const (Int (to_int (eval e1) / to_int (eval e2)))
  | Op2 (Mod, e1, e2) -> Const (Int (to_int (eval e1) mod to_int (eval e2)))
  | If (e1, e2, e3) -> if to_bool (eval e1) then eval e2 else eval e3
  | Let (id, e1, e2) -> eval (subst id (eval e1) e2)
  | Empty -> Empty
  | Cons (hd, tl) -> let _ = to_list (tl) in Cons (eval hd, eval tl)
  | Head e -> extract_head (eval e)
  | Tail e -> extract_tail (eval e)
  | IsEmpty e -> is_empty (eval e)
  | Record e -> Record e
  | GetField (r, f) -> eval (List.assoc f (to_record (eval r)))
  | Fun (param, body) -> Fun (param, body)
  | Fix (name, body) -> Fix (name, body)
  | App (fn, arg) ->
    (match eval fn with
    | Fun (param, body) -> eval (subst param (eval arg) body)
    | Fix (name, body) -> eval (App (subst name (Fix (name, body)) body, arg))
    | _ -> failwith "invalid function call")
  | Id x -> failwith ( " free identifier " ^ x)
  | _ -> failwith "not implemented"

let get_output (program: exp): string = 
  let v = eval program in
  match v with
    | Const (Int n) -> sprintf "%d" n
    | Const (Bool b) -> sprintf "%b" b
    | Id s -> s
    | _ -> let () = pp_exp Format.str_formatter v in Format.flush_str_formatter ()

let eval_str (s: string): string = 
  get_output (from_string s)

let%TEST "list length" = eval_str "let length_tail = fix len -> fun li -> fun acc -> if empty?li then acc else (len (tail li) (acc + 1)) in let length = fun li -> length_tail li 0 in length (1 :: 2 :: 3 :: empty)" = "3"

let%TEST "list filter" = eval (from_string "let filter_tail = fix fil -> fun f -> fun li -> fun acc -> if empty?li then acc else let hd = head li in let new_acc = if f hd then hd :: acc else acc in fil f (tail li) new_acc in let filter = fun f -> fun li -> filter_tail f li empty in filter (fun x -> x > 2) (1 :: 2 :: 3 :: (2 + 2) :: empty)") = Cons (Const (Int 4), Cons (Const (Int 3), Empty))

let%TEST "reverse list with tail recursion" = eval (from_string "let reverse_tail = fix rev -> fun li -> fun acc -> if empty?li then acc else rev (tail li) ((head li) :: acc) in let reverse = fun li -> reverse_tail li empty in reverse (4 :: 3 :: empty)") = Cons (Const (Int 3), Cons (Const (Int 4), Empty))

let%TEST "list a" = eval_str "let x = let x = 40 + 2 in x :: 200 :: empty in head x == 42" = "true"
let%TEST "list b" = eval_str "let x = 100 :: 200 :: empty in empty?x" = "false"
let%TEST "add" = eval_str "let x = 1 + 1 in x * 4" = "8"
let%TEST "fun a" = eval_str "let x = 2 in let f = fun x -> x + 2 in f 4 + x" = "8"
let%TEST "fun b" = eval_str "(fun x -> (fun x -> x + 100) (x * 100)) 6" = "700"
let%TEST "fun c" = eval_str "let x = 100 in let f = fun y -> y + (y - 1) % y in f x" = "199"
let%TEST "curry a" = eval_str "let f = fun a -> fun b -> fun c -> a + b + c  in f 2 3 3" = "8"
let%TEST "rec a" = eval_str "let r = {a: 200, b: 100, c: 0} in r.a" = "200"
let%TEST "rec b" = eval_str "let x = 100 in let r = {a: x + 200, x: 200} in r.a" = "300"
let%TEST "rec c" = eval_str "let f = fun x -> {a: x} in (f 8).a" = "8"
let%TEST "fix a" = eval_str "(fix fact -> fun y -> if y == 0 then 1 else y * (fact (y -1))) 4" = "24"
let%TEST "fix b" = eval_str "let fact = fix f -> fun y ->  if y == 0 then 1 else y * (f (y - 1)) in fact 7" = "5040"

let _ =
    try
      let filename : string = Sys.argv.(1) in
      let output = get_output (from_file filename) in
      printf "%s\n" output
    with
      Invalid_argument explanation -> Ppx_test.Test.collect ()
