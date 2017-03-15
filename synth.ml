(* To compile this file, run:
 *
 * ocamlbuild -use-ocamlfind -pkg compsci631 -pkg ppx_test synth.d.byte
 *
 * This produces an executable called synth.d.byte.
 *)
open Smtlib
open Sketching
open Printf

type value = 
  | Const of int
  | Falsum
  [@@deriving show]

type state = (id * value) list
  [@@deriving show]

module Set = Set.Make(String)
let args = ref Set.empty
let holes = ref Set.empty
(* let loop_sentinels = Hashtbl.create 4242*)
let w = ref 0 
let upper_bound = int_of_float (2. ** (float_of_int 16)) - 1
let skip_value (w: int): term = bv (int_of_float (2. ** (float_of_int w)) - 1) w
let abort_value (w: int): term = bv (int_of_float (2. ** (float_of_int w)) - 2) w
let id_bexp_map = Hashtbl.create 4242

(* let synth = Smtlib.make_solver "z3"*)
(* let verif = Smtlib.make_solver "z3"*)
let synth = Smtlib.make_solver "./z3_debug_synth.sh"
let verif = Smtlib.make_solver "./z3_debug_verif.sh"

let my_bv (n: int) (w: int): term =
  if n >= 0 then
    bv n w
  else
    bvadd (bvnot (bv (-1 * n) w)) (bv 1 w)

let rec subst_id (x: id) (i: exp) (e: exp): exp =
  match e with
  | EId id -> if id = x then i else e
  | EOp2 (op2, e1, e2) -> EOp2 (op2, subst_id x i e1, subst_id x i e2)
  | EOp1 (op1, e1) -> EOp1 (op1, subst_id x i e1)
  | _ -> e

let rec subst_cmd (x: id) (i: exp) (c: cmd): cmd =
  match c with
  | CAssign (y, e) -> CAssign (y, subst_id x i e)
  | CIf (b, c1, c2) -> CIf (subst_id x i b, subst_cmd x i c1, subst_cmd x i c2)
  | CSeq (c1, c2) -> CSeq (subst_cmd x i c1, subst_cmd x i c2)
  | CRepeat (y, e, c1) -> CRepeat (y, subst_id x i e, subst_cmd x i c1)
  | _ -> c

let get_random_input () : (string * int) list =
  let l = ref [] in
  (* let _ = List.iter (fun x -> x := (x, Random.int 4242) :: !x) !args in*)
  let _ = Set.iter (fun x -> l := (x, 1) :: !l) !args in
  if List.length !l = 0 && Set.cardinal !holes > 0 then [("dummy", 1)] else !l

let term_to_string (t: term): string =
  sexp_to_string (term_to_sexp t)

let term_to_int (t: term): int =
  match t with
  | Int n -> n
  | BitVec (n, w) -> n
  | _ -> failwith "term_to_int fail"

let id_to_term (id: id): term = Const (Id id)

let intersect (s1: state) (s2: state): state =
  List.filter (fun (k, v) -> if List.mem_assoc k s2 then true else false) s1

let eval_const (op2: op2) (n1: int) (n2: int): int =
  match op2 with
  | Add -> n1 + n2
  | Sub -> n1 - n2
  | Mul -> n1 * n2
  | Div -> n1 / n2
  | Mod -> n1 mod n2
  | LShift -> n1 lsl n2
  | RShift -> n1 lsr n2
  | BAnd -> n1 land n2
  | BOr ->  n1 land n2
  | LAnd -> if n1 > 0 && n2 > 0 then 1 else 0
  | LOr -> if n1 > 0 || n2 > 0 then 1 else 0 
  | Eq -> if n1 = n2 then 1 else 0

let rec p_eval_exp (e: exp) (s: state) (predicate: value): value * exp =
  (* let _ = pp_exp Format.std_formatter e in*)
  match e with
  | EId id -> (
      if List.mem_assoc id s
      then
        let v = List.assoc id s in
        match v with
        | Const n ->  (Const n, EInt n)
        | Falsum -> (Falsum, e)
      else
        let _  = if Set.mem id !holes then () else args := Set.add id !args; in
        (Falsum, e)
  )
  | EInt n -> (Const n, e)
  | EOp2 (op2, e1, e2) -> (
      let v1, e1' = p_eval_exp e1 s predicate in
      let v2, e2' = p_eval_exp e2 s predicate in
      match predicate, v1, v2 with
      | Const 1, Const n1, Const n2 -> let n = eval_const op2 n1 n2 in (Const n, EInt n)
      | _, _ , _ -> Falsum, EOp2 (op2, e1', e2')
  )
  | EHole id -> let id = "c" ^ (string_of_int id) in let _ = holes := Set.add id !holes in (Falsum, EId id)
  | EOp1 (op1, e1) -> (
      let v1, e1' = p_eval_exp e1 s predicate in
      match predicate, v1 with
      | Const 1, Const n -> let n = (
          match op1 with
          | LNot -> if n > 0 then 0 else 1
          | BNot -> lnot n
        ) in (Const n, EInt n)
      | _, _ -> (Falsum, EOp1 (op1, e1'))
    )
  | EWidth -> Const !w, EWidth
  
let rec p_eval (c: cmd) (s: state) (predicate: value): cmd * state =
  match c with
  | CAssign (x, e) ->
      let v, e' = p_eval_exp e s predicate in CAssign (x, e'), ((x, v) :: s)
  | CIf (b, c1, c2) -> (
      let v, e = p_eval_exp b s predicate in
      match v with
      | Const n -> if n > 0 then p_eval c1 s predicate else p_eval c2 s predicate
      | Falsum ->
            let c1', s1' = p_eval c1 s Falsum in
            let c2', s2' = p_eval c2 s Falsum in
            CIf (e, c1', c2'), intersect s1' s2'
    )
  | CSeq (c1, c2) -> let c1', s1' = p_eval c1 s predicate in let c2', s2' = p_eval c2 s1' predicate in  CSeq (c1', c2'), s2'
  | CRepeat (x, e, body) -> (
      let v, e' = p_eval_exp e s predicate in
      match v with
      | Const n -> (
          let c' = ref CSkip in
          let s' = ref s in
          let _ = for i = 0 to n - 1 do 
            (* let x' = x ^ (string_of_int i) in*)
            (* let _ = c' := CSeq(CAssign (x', EInt i)) in*)
            let body' = subst_cmd x (EInt i) body in
            let body'', s'' = p_eval body' !s' predicate in
            s' := s'';
            c' := CSeq (!c', body'');
          done in
          (!c', !s')
        )
      | Falsum -> if Set.mem x !args then
                    (c, s)
                  else
                    let gt_0 (e1: exp): exp = EOp2 (LOr, e1, (EInt 0)) in
                    let lt_0 (e1: exp): exp = EOp1 (LNot, (EOp2 (LOr, e1, (EInt 0)))) in
                    let t0 = x ^ "0" in
                    let body' = subst_cmd x (EId t0) body in
                    let cmd  = ref (CSeq (CAssign (t0, EOp2 (Sub, e', EInt 1)), CIf (gt_0 (EId t0), body', CSkip))) in
                    (* let unroll_limit = !w in*)
                    let unroll_limit = 2 in
                    let _ = for i = 1 to unroll_limit do
                      let ti =  x ^ (string_of_int i) in
                      let body' = subst_cmd x (EId ti) body in
                      let tim1 = x ^ (string_of_int (i - 1)) in
                      cmd := CSeq (!cmd, CSeq (CAssign (ti, EOp2 (Sub, EId tim1, EInt 1)), CIf (gt_0 (EId ti), body', CSkip)))
                    done in
                    (CSeq (!cmd, CIf (lt_0 (EId (x ^ (string_of_int unroll_limit))), CSkip, CAbort)), s)
    )
  | CSkip -> (c, s)
  | CAbort -> (c, s)


let rec exp_to_bexp (e: exp): term =
  (* let _ = pp_exp Format.std_formatter e in*)
  let bv0 = bv 0 !w in
  let bv1 = bv 1 !w in
  match e with
  | EId id -> if Hashtbl.mem id_bexp_map id then Hashtbl.find id_bexp_map id else id_to_term id
  | EInt n -> my_bv n !w
  | EOp2 (op2, e1, e2) -> (
      let b1 = exp_to_bexp e1 in
      let b2 = exp_to_bexp e2 in
      match op2 with
      | Add -> bvadd b1 b2
      | Sub -> bvsub b1 b2 
      | Mul -> bvmul b1 b2
      | Div -> assert_ synth (bvugt b2 bv0); assert_ verif (bvugt b2 bv0); bvsdiv b1 b2
      | Mod -> assert_ synth (bvugt b2 bv0); assert_ verif (bvugt b2 bv0); bvsmod b1 b2
      | LShift -> bvshl b1 b2
      | RShift -> bvlshr b1 b2
      | BAnd -> bvand b1 b2
      | BOr ->  bvor b1 b2
      | LAnd -> ite (and_ (bvugt b1 bv0) (bvugt b2 bv0)) bv1 bv0
      | LOr -> ite (or_ (bvugt b1 bv0) (bvugt b2 bv0)) bv1 bv0
      | Eq -> ite (equals b1 b2) bv1 bv0
    )
  | EOp1 (op1, e1) -> (
      let b1 = exp_to_bexp e1 in
      match op1 with
      | LNot -> ite (bvugt b1 bv0) bv0 bv1
      | BNot -> bvnot b1
    )
  | EWidth -> bv !w !w
  | EHole id -> let id = "c" ^ (string_of_int id) in let _ = holes := Set.add id !holes in id_to_term id

let rec cmd_to_bexp ?(predicate: term option) (c: cmd): term =
  match c with
  | CAssign (x, e) -> (
      let b = exp_to_bexp e in
      match predicate with
      | None -> let _ = Hashtbl.add id_bexp_map x b in b
      | Some cond -> (
          let alt = if Hashtbl.mem id_bexp_map x then Hashtbl.find id_bexp_map x else (bv 0 !w) in 
          let b' = ite cond b alt in 
          Hashtbl.add id_bexp_map x b'; b'
        )
    )
  | CIf (e, c1, c2) -> (
      let b = exp_to_bexp e in
      let bb = bvugt b (bv 0 !w) in
      let t1 = cmd_to_bexp c1 ~predicate:bb in
      let t2 = cmd_to_bexp c2 ~predicate:(not_ bb) in
      ite bb t1 t2
    )
  | CRepeat (x, e, c) -> skip_value !w
  | CSeq (c1, c2) -> (
      let cb1 = cmd_to_bexp c1 in
      match c1 with 
      | CAbort -> cb1
      | _ -> (
        match c2 with
        | CSkip -> cb1
        | _ -> cmd_to_bexp c2
      )
    )
  | CAbort -> abort_value !w
  | CSkip -> skip_value !w

let rec generate_bexp_for_one_input (sketch: cmd) (spec: cmd) (input: (string * int) list): unit = 
  let input_state = List.map (fun (k, v) -> (k, Const v)) input in
  let sketch, s = p_eval sketch input_state (Const 1) in
  (* let _ = pp_cmd Format.std_formatter spec in*)
  let spec, s = p_eval spec input_state (Const 1) in
  (* let _ = pp_cmd Format.std_formatter sketch in*)
  let _ = Hashtbl.clear id_bexp_map in
  let sketch_b = cmd_to_bexp sketch in
  let _ = fprintf stderr "sketch: %s\n" (term_to_string sketch_b) in
  let _ = Hashtbl.clear id_bexp_map in
  let spec_b = cmd_to_bexp spec in
  let _ = fprintf stderr "spec: %s\n" (term_to_string spec_b) in
  assert_ synth (equals sketch_b spec_b)

let synthesize_for_some_inputs (sketch: cmd) (spec: cmd) (inputs: (string * int) list list): (string * int) list =
  let _ = List.iter (fun input -> generate_bexp_for_one_input sketch spec input) inputs in
  match check_sat synth with
  | Unsat -> let _ = fprintf stderr "some_inputs: unsat!\n" in []
  | Sat ->
      let model = get_model synth in
      let model = List.filter (fun (Smtlib.Id x, t) -> if Set.mem x !holes then true else false) model in
      let _ = fprintf stderr "some_inputs: sat: %d\n" (List.length model) in
      let _ = List.iter (fun (Smtlib.Id x, t) -> fprintf stderr "Model: %s: %s\n" x (term_to_string t)) model in
      let model = ref (List.map (fun (Smtlib.Id x, t) -> x, term_to_int t) model) in
      (* if a value was not guessed because it is obvious, use 0 *)
      let _ = Set.iter (fun h -> if List.mem_assoc h !model then () else model := (h, 0) :: !model) !holes in
      !model
  | Unknown -> let _ = fprintf stderr "unknown" in []

let verify_for_all_inputs (sketch: cmd) (spec: cmd) (c: (string * int) list): (string * int) list = 
  let _ = Hashtbl.clear id_bexp_map in
  let sb = cmd_to_bexp sketch in
  let _ = Hashtbl.clear id_bexp_map in
  let pb = cmd_to_bexp spec in
  let _ = List.iter (fun (x, n) -> assert_ verif (equals (id_to_term x) (my_bv n !w))) c in
  let _ = assert_ verif (not_ (equals sb pb)) in
  match check_sat verif with
  | Unsat -> let _ = fprintf stderr "all_inputs: unsat!\n" in []
  | Sat -> 
      let model = get_model verif in
      let model = List.filter (fun (Smtlib.Id x, t) -> if Set.mem x !args then true else false) model in
      let _ = fprintf stderr "all_inputs: sat: %d\n" (List.length model) in
      let _ = List.iter (fun (Smtlib.Id x, t) -> fprintf stderr "Model: %s: %s\n" x (term_to_string t)) model in
      let model = ref (List.map (fun (Smtlib.Id x, t) -> x, term_to_int t) model) in
      (* if a value was not guessed because it is obvious, use 0 *)
      let _ = Set.iter (fun i -> if List.mem_assoc i !model then () else model := (i, 0) :: !model) !args in
      !model
  | Unknown -> let _ = fprintf stderr "unknown" in []

let declare_consts (s: solver): unit = 
  Set.iter (fun id -> declare_const s (Smtlib.Id id) (bv_sort !w); assert_ s (bvule (id_to_term id) (bv upper_bound !w))) !args;
  Set.iter (fun id -> declare_const s (Smtlib.Id id) (bv_sort !w); assert_ s (bvule (id_to_term id) (bv upper_bound !w))) !holes;
  ()

let synthesize (sketch: cmd) (spec: cmd): (string * int) list =
  let _ = declare_consts synth in
  let _ = declare_consts verif in
  let inputs = ref [] in
  let x = ref (get_random_input ()) in
  let c = ref [] in
  if List.length !x = 0 then
    failwith "cannot generate random inputs to begin. probably buggy sketch"
  else
    let _ = while List.length !x != 0 do
      let _ = inputs := !x :: !inputs  in
      let _ = c := synthesize_for_some_inputs sketch spec !inputs in
      if List.length !c = 0 then
        failwith "synthesizer could not generate values for the holes"
      else
        x := verify_for_all_inputs sketch spec !c;
    done in
    !c

let rec subst_holes_exp (e: exp) (c: (string * int) list): exp =
  (* let _ = pp_exp Format.std_formatter e in*)
  match e with 
  | EId id -> if List.mem_assoc id c then EInt (List.assoc id c) else e
  | EInt n -> e
  | EHole id -> e
  | EOp2 (op2, e1, e2) -> EOp2 (op2, subst_holes_exp e1 c, subst_holes_exp e2 c)
  | EOp1 (op1, e1) -> EOp1 (op1, subst_holes_exp e1 c)
  | EWidth -> e

let rec subst_holes (sketch: cmd) (c: (string * int) list):  cmd =
  match sketch with
  | CAssign (id, e) ->  CAssign (id, subst_holes_exp e c)
  | CIf (e, c1, c2) -> CIf (subst_holes_exp e c, subst_holes c1 c, subst_holes c2 c)
  | CSeq (c1, c2) -> CSeq (subst_holes c1 c, subst_holes c2 c)
  | CRepeat (x, e, c1) -> CRepeat (x, subst_holes_exp e c, subst_holes c1 c)
  | _ -> sketch

let cegis (width : int) (sketch : cmd) (spec : cmd) : Sketching.cmd option =
    let _ = w := width in
    let spec', s_spec = p_eval spec [] (Const 1) in
    let sketch', s_sketch = p_eval sketch [] (Const 1) in
    (* let _ = pp_cmd Format.std_formatter spec in*)
    (* let _ = pp_cmd Format.std_formatter spec' in*)
    (* let _ = pp_cmd Format.std_formatter sketch' in*)
    (* Some sketch'*)
    let c = synthesize sketch' spec' in
    Some (subst_holes sketch' c)

let _ =
  let width = int_of_string Sys.argv.(1) in
  let sketch = Sketching.from_file Sys.argv.(2) in
  let spec = Sketching.from_file Sys.argv.(3) in
  (* let _ = pp_cmd Format.std_formatter sketch in*)
  try
  match cegis width sketch spec with
    | None -> (printf "Synthesis failed.\n%!"; exit 1)
    | Some sketch' ->
      print_endline (Sketching.to_string sketch')
  with Failure f ->
      print_endline ("Synthesis failed: " ^ f); exit 1
