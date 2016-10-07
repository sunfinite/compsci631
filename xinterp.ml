(* To compile this file, run:
 *
 * ocamlbuild -use-ocamlfind -pkg compsci631 -pkg ppx_test xinterp.d.byte
 *
 * This produces an executable called xinterp.d.byte.
 *
 * You can use write inline unit tests using the same technique you used
 * in the first assignment
 *)

module PTest = Ppx_test.Test
open Xinterp_util
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
  | MkArray (e1, e2) -> MkArray (e1, e2)
  | GetArray (e1, e2) -> GetArray (e1, e2)
  | SetArray (e1, e2, e3) -> SetArray (e1, e2, e3)
  | Id y -> if x = y then v else Id y
  | _ -> failwith "we don't know how to substitute for this yet! get cracking."

let add_to_store (nesting: int) (id: id) (length: int) (default: 'a) (mutations: 'b list) (store: 'c list): 'c list =
   (* FIXME: di not overwrite the whole bucket *)
   let _ = List.remove_assoc nesting store in
   (nesting, [(id, (length, default, mutations))]) :: store 

let check_array_bounds (length: int) (index: int): bool = 
  match (index < 0 || index >= length) with
  | false -> true
  | true -> failwith "invalid array index"

let rec lookup_store (id: id) (store: 'c list) (nesting: int) =
  match (nesting < 0) with
  | true ->  failwith ("unknown id: "  ^ id)
  | false ->
      if List.mem_assoc nesting store
      then
        let vars = List.assoc nesting store in
        if List.mem_assoc id vars
        then
          (nesting, vars)
        else
          lookup_store id store (nesting - 1)
      else
        lookup_store id store (nesting - 1)

let rec eval (e: exp) (store: 'a list) (nesting: int): (exp * 'a list) =
  (* let _ = pp_exp Format.std_formatter e in*)

  let evalp (e: exp) (store: 'a list) = eval e store nesting in

  let delta_bool e1 e2 op: (exp * 'a list) =
    let c1, store = evalp e1 store in
    let c2, store = evalp e2 store in
    let res = (op) (to_int c1) (to_int c2) in
    (Const (Bool res), store)
  in

  let delta_int e1 e2 op: (exp * 'a list) =
    let c1, store = evalp e1 store in
    let c2, store = evalp e2 store in
    let res = (op) (to_int c1) (to_int c2) in
    Const (Int res), store
  in

  match e with
  | Const c ->  (Const c, store)
  | Op2 (LT, e1, e2) -> delta_bool e1 e2 (<)
  | Op2 (GT, e1, e2) -> delta_bool e1 e2 (>)
  | Op2 (Eq, e1, e2) -> delta_bool e1 e2 (=)
  | Op2 (Add, e1, e2) -> delta_int e1 e2 (+)
  | Op2 (Sub, e1, e2) -> delta_int e1 e2 (-)
  | Op2 (Mul, e1, e2) -> delta_int e1 e2 ( * )
  | Op2 (Div, e1, e2) -> delta_int e1 e2 (/)
  | Op2 (Mod, e1, e2) -> delta_int e1 e2 (mod)
  | If (e1, e2, e3) ->
      let c, store = evalp e1 store in
      if (to_bool c) then (evalp e2 store) else (evalp e3 store)
  | Let (id, e1, e2) -> (
      let e1, store = evalp e1 store in
      match e1 with
      | MkArray (length, default) ->
          let length, store = evalp length store in
          let default, store = evalp default store in
          let store = add_to_store nesting id (to_int length) default [] store in
          let res, store = eval e2 store (nesting + 1) in
          res, List.remove_assoc nesting store
      | SetArray (name, i, set_exp) -> (
          let name, store = evalp name store in
          match name with
          | Id id ->
              let nestingp, vars = lookup_store id store nesting in
              let length, default, mutations = List.assoc id vars in
              let index, store = evalp i store in 
              let index = to_int index in
              let _ = check_array_bounds length index in
              let c, store = evalp set_exp store in
              let store = add_to_store nestingp id length default ((index, c) :: mutations) store in
              eval e2 store (nesting + 1)
          | MkArray (length, default) -> failwith "cannot set values of anonymous arrays"
          | _ -> failwith "invalid array name"
        )
      | Id id2 ->
          let nestingp, vars = lookup_store id2 store nesting in 
          let length, default, mutations = List.assoc id2 vars in
          let store = add_to_store nesting id length default mutations store in
          eval e2 store (nesting + 1)
      | _ -> eval (subst id e1 e2) store (nesting + 1)
    )
  | Empty -> Empty, store
  | Cons (hd, tl) ->
      let _ = to_list (tl) in
      let hd, store = evalp hd store in
      let tl, store = evalp tl store in
      Cons (hd, tl), store
  | Head e ->
      let e, store = evalp e store in
      extract_head e, store
  | Tail e ->
      let e, store = evalp e store in
      extract_tail e, store
  | IsEmpty e ->
      let e, store = evalp e store in
      is_empty e, store
  | Record e -> Record e, store
  | GetField (r, f) -> 
    let r, store = evalp r store in
    evalp (List.assoc f (to_record r)) store
  | Fun (param, body) -> Fun (param, body), store
  | Fix (name, body) -> Fix (name, body), store
  | App (fn, arg) -> (
      let fn, store = evalp fn store in
      match fn with
      | Fun (param, body) -> evalp (Let (param, arg, body)) store
      | Fix (name, body) -> evalp (App (subst name (Fix (name, body)) body, arg)) store
      | _ -> failwith "invalid function call"
    )
  | MkArray (e1, e2) -> MkArray (e1, e2), store
  | GetArray (e1, e2) -> (
      let e1, store = evalp e1 store in
      let e2, store = evalp e2 store in
      let index = to_int e2 in
      match e1 with
      | Id id ->
          let nesting, vars = lookup_store id store nesting in
          let length, default, mutations = List.assoc id vars in
          let _ = check_array_bounds length index in
          if List.mem_assoc index mutations 
          then
            (List.assoc index mutations), store
          else 
            default, store
      | MkArray (length, default) ->
          let length, store = evalp length store in
          let _ = check_array_bounds (to_int length) index in
          evalp default store
      | _ -> failwith ("invalid array name")
    )
  | SetArray (e1, e2, e3) -> SetArray (e1, e2, e3), store
  | Id x -> let _ = lookup_store x store nesting in (Id x), store
  | _ -> failwith "not implemented"

let get_output (program: exp): string =
  let v, store = (eval program [] 0) in
  match v with
    | Const (Int n) -> sprintf "%d" n
    | Const (Bool b) -> sprintf "%b" b
    | Id s -> s
    | _ -> let () = pp_exp Format.str_formatter v in Format.flush_str_formatter ()

let eval_str (s: string): string =
  get_output (from_string s)
  
let eval_exp (s: string): exp = 
  let v, store = eval (from_string s) [] 0 in
  v

let%TEST "list length" = eval_str "let length_tail = fix len -> fun li -> fun acc -> if empty?li then acc else (len (tail li) (acc + 1)) in let length = fun li -> length_tail li 0 in length (1 :: 2 :: 3 :: empty)" = "3"

let%TEST "list filter" = eval_exp "let filter_tail = fix fil -> fun f -> fun li -> fun acc -> if empty?li then acc else let hd = head li in let new_acc = if f hd then hd :: acc else acc in fil f (tail li) new_acc in let filter = fun f -> fun li -> filter_tail f li empty in filter (fun x -> x > 2) (1 :: 2 :: 3 :: (2 + 2) :: empty)" = Cons (Const (Int 4), Cons (Const (Int 3), Empty))

let%TEST "reverse list with tail recursion" = eval_exp "let reverse_tail = fix rev -> fun li -> fun acc -> if empty?li then acc else rev (tail li) ((head li) :: acc) in let reverse = fun li -> reverse_tail li empty in reverse (4 :: 3 :: empty)" = Cons (Const (Int 3), Cons (Const (Int 4), Empty))

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
let%TEST "free identifier in function" = (try (eval_str "(fun x -> x + y) 5") with Failure f -> f) = "unknown id: y"
let%TEST "free identifier outside" = (try (eval_str "1 <w 2") with Failure f -> f) = "unknown id: w"

let%TEST "array a" = eval_str "let ar = array(10, 100) in ar[0]" = "100"
let%TEST "array b" = eval_str "array(10, 100)[0]" = "100"
let%TEST "array c" = eval_str "let ar = array(10, 100) in let _ = ar[1]= 200 in let br = ar in br[1]" = "200"
let%TEST "array c" = eval_str "let ar = array(10, 100) in let br = array(10, ar) in let _ = br[0][0] = 200 in br[0][0]" = "200"
let%TEST "array d" = eval_str "let ar = array(10, 100) in let br = array(10, ar) in let cr = array(10, br) in let _ = br[0][0] = 200 in cr[1][1][0]" = "200"
let%TEST "array e" = eval_str "let f = fun x -> let _ = ar[1] = 200 in 1 in let ar = array(10, 100) in let x = f ar in ar[1] + x" = "201"
let%TEST "array_bounds_check a" = (try (eval_str "array(10, 100)[100]") with Failure f -> f) = "invalid array index"
let%TEST "array_bounds_check b" = (try (eval_str "let ar = array(10, 100) in ar[10]") with Failure f -> f) = "invalid array index"
let%TEST "array_bounds_check c" = (try (eval_str "let ar = array(10, 100) in let _ = ar[10] = 200 in ar[0]") with Failure f -> f) = "invalid array index"
let%TEST "set_array a" = eval_str "let ar = array(10, 100) in let f = ((fun x -> let _ = ar[1] = 200 in x) 100) in ar[1]" = "200"
let%TEST "set_array b" = eval_str "let ar = array(10, 100) in let f = fun x -> (let _ = ar[1] = 200 in 100) in let x = (let _ = ar[2] = 400 in f 5) in ar[1] + ar[2] + x" = "700"
let%TEST "set_array out of scope" = (try (eval_str "let f = fun x -> let ar = array(10, 10) in 1 in let x = f 5  in let _ = ar[1]  = 5 in x") with Failure f -> f) = "unknown id: ar"

let _ =
    try
      let filename : string = Sys.argv.(1) in
      let output = get_output (from_file filename) in
      printf "%s\n" output
    with
      Invalid_argument explanation -> Ppx_test.Test.collect ()
