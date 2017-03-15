(* To compile this file, run:
 *
 * ocamlbuild -use-ocamlfind -pkg compsci631 -pkg ppx_test verif.d.byte
 *
 * This produces an executable called verif.d.byte.
 *)

open Smtlib
open Imp
open Printf
open Format

let z3_path = "z3"
(* let z3_path = "./z3_debug.sh"*)

let solver = make_solver z3_path

let consts = ref []

let var_counter = ref 0

let get_var (): Imp.aexp =
  var_counter := !var_counter + 1;
  Imp.AVar ("v" ^ (string_of_int !var_counter))

let rec subst_aexp (id: string) (exp: Imp.aexp) (orig: Imp.aexp): Imp.aexp =
  match orig with
  | AVar id1 -> if id = id1 then exp else orig
  | AConst n -> orig
  | AOp (op, e1, e2) -> AOp (op, subst_aexp id exp e1, subst_aexp id exp e2)

let rec subst (post: Imp.bexp) (id: string) (exp: Imp.aexp): Imp.bexp =
  match post with
  | BCmp (cmp, e1, e2) -> BCmp (cmp, subst_aexp id exp e1, subst_aexp id exp e2)
  | BConst b -> BConst b
  | BAnd (b1, b2) -> BAnd (subst b1 id exp, subst b2 id exp)
  | BOr (b1, b2) -> BOr (subst b1 id exp, subst b2 id exp)
  | BNot b -> BNot (subst b id exp)
  | _ -> failwith "substitution failed"

let rec subst_assigned (ids: string list) (p: Imp.bexp): Imp.bexp =
  match ids with
  | [] -> p
  | [id] -> subst p id (get_var ())
  | hd :: tl -> subst (subst_assigned tl p) hd (get_var ())

let rec aexp_to_term (aexp: Imp.aexp) : Smtlib.term =
  match aexp with 
  | AConst n -> int_to_term n
  | AVar id -> 
      if List.mem_assoc id !consts
      then ()
      else (
        consts := (id, 1) :: !consts;
        declare_const solver (Smtlib.Id id) int_sort; 
      );
      Smtlib.Const (Smtlib.Id id)
  | AOp (op, e1, e2) -> (
      let ta1 = aexp_to_term e1 in
      let ta2 = aexp_to_term e2 in
      match op with
      | Add -> add ta1 ta2
      | Sub -> sub ta1 ta2
      | Mul -> mul ta1 ta2
  )
  | _ -> failwith "Unknown aexp"

let rec get_assigned (cmd: Imp.cmd) (acc: string list): string list = 
  match cmd with
  | CAssign (id, e) -> id :: acc
  | CSeq (c1, c2) -> (get_assigned c1 acc) @ (get_assigned c2 acc) @ acc
  | CIf (b, c1, c2) -> (get_assigned c1 acc) @ (get_assigned c2 acc) @ acc
  | CWhile (i, b, c) -> (get_assigned c acc) @ acc
  | _ -> acc

let rec wp (cmd: Imp.cmd) (pred_list: Imp.bexp * Imp.bexp list): (Imp.bexp * Imp.bexp list) =
  let (post, l) = pred_list in
  (* let _ = pp_cmd std_formatter cmd in*)
  match cmd with
  | CAssign (id, e) -> (subst post id e, l)
  | CSeq (c1, c2) -> wp c1 (wp c2 (post, l))
  | CIf (b, c1, c2) -> 
      let p1, l1 = wp c1 (post, l) in
      let p2, l2 = wp c2 (post, l) in
      (BOr (BAnd (b, p1), BAnd (BNot b, p2)), l1 @ l2)
  | CWhile (b, i, c) -> (
      let ids = get_assigned c [] in
      (* let _ = List.iter (fun s -> printf "Assigned: %s" s) ids in*)
      let p1, l1 = wp c (i, l) in
      (* let r1 = subst_assigned ids (BOr (BNot (BAnd (i, b)), p1)) in*)
      (* let r2 = subst_assigned ids (BOr (BNot (BAnd (i, BNot b)), post)) in*)
      let r1 = (BOr (BNot (BAnd (i, b)), p1)) in
      let r2 = (BOr (BNot (BAnd (i, BNot b)), post)) in
      (i,  r1 :: r2 :: l1)
    )
  | CSkip -> (post, l)
  | CAbort -> (BConst false, l)
  (* While abort assert *)
  | _ -> failwith "wp failed"

let rec bexp_to_term (bexp : Imp.bexp) : Smtlib.term =
  (* let _ = printf "Bexp to term: %s\n" (bexp_to_string bexp) in*)
  match bexp with
  | BCmp (cmp, e1, e2) -> (
      let t1 = aexp_to_term e1 in
      let t2 = aexp_to_term e2 in
      match cmp with
      | Lt -> lt t1 t2
      | Lte -> lte t1 t2
      | Gt -> gt t1 t2
      | Gte -> gte t1 t2
      | Eq -> equals t1 t2
    )
  | BAnd (b1, b2) -> and_ (bexp_to_term b1) (bexp_to_term b2)
  | BOr (b1, b2) -> or_ (bexp_to_term b1) (bexp_to_term b2)
  | BNot b -> not_ (bexp_to_term b)
  | BConst b -> bool_to_term b
  | _ -> failwith "bexp_to_term: not implemented"

let term_to_string (t: term): string = 
  sexp_to_string (term_to_sexp t)

let sat (p: term) (q: term): bool = 
  let _ = push solver in
  let _ = assert_ solver (not_ (implies p q)) in
  let r  = check_sat solver in
  let ret = match r with
  | Unsat -> true
  | Sat -> 
      (* let model = get_model solver in*)
      (* let _ = List.iter (fun (Smtlib.Id x, t) -> printf "Model: %s: %s\n" x (term_to_string t)) model in*)
      false
  | Unknown -> false
  in
  let _ = pop solver in
  ret

let verify (pre : bexp) (cmd : cmd) (post : bexp) : bool =
  let wp, lps = wp cmd (post, []) in
  let _ = printf "\nPre: %s\n" (bexp_to_string pre) in
  let _ = printf "Post: %s\n" (bexp_to_string post) in
  let _ = printf "WP: %s\n" (bexp_to_string wp) in
  (* push solver;*)
  let pre_term = bexp_to_term pre in
  let wp_term = bexp_to_term wp in
  (* let _ = printf "\nTerm: %s\n" (term_to_string wp_term) in*)
  (* let _ = printf "\nPre Term: %s\n" (term_to_string pre_term) in*)
  (* let _ = push solver in*)
  (* let _ = assert_ solver pre_term in*)
  (* let _ = assert_ solver (implies pre_term wp_term) in*)
  (* let _ = pop solver in*)
  let failed = ref false in
  (* let _ = List.iter (fun t -> push solver; if not (sat pre_term (bexp_to_term t)) then failed := not !failed else (); pop solver) lps in*)
  let _ = List.iter (fun t -> if not (sat pre_term (bexp_to_term t)) then failed := true else ()) lps in
  let ret = if !failed = true 
    then 
      false
    else sat pre_term wp_term
  in
  (* pop solver;*)
  ret

let _ =
  let filename = Sys.argv.(1) in
  let (pre, cmd, post) = from_file filename in
  if verify pre cmd post then
    (printf "Verification SUCCEEDED.\n%!"; exit 0)
  else
    (printf "Verification FAILED.\n%!"; exit 1)
