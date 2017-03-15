(* To compile this file, run:
 *
 * ocamlbuild -use-ocamlfind -pkg compsci631 -pkg ppx_test typeinf.d.byte
 *)
module Explicit = Tc_util
module Implicit = Xinterp_util
open Printf

(* This is necessary for let%TEST to work. *)
module PTest = Ppx_test.Test

let metavar_counter = ref 0

let generate_metavar (): Explicit.typ =
  let _ = incr metavar_counter in
  Explicit.TMetavar (string_of_int !metavar_counter)

let rec add_metavars (exp : Implicit.exp) : Explicit.exp = match exp with
  | Implicit.Const c -> Explicit.Const c
  | Implicit.Id id -> Explicit.Id id
  | Implicit.Op2 (op, e1, e2) -> Explicit.Op2 (op, add_metavars e1, add_metavars e2)
  | Implicit.If (e1, e2, e3) -> Explicit.If (add_metavars e1, add_metavars e2, add_metavars e3)
  | Implicit.Fun (param, body) -> Explicit.Fun (param, generate_metavar (), add_metavars body)
  | Implicit.Fix (name, body) -> Explicit.Fix (name, generate_metavar (), add_metavars body)
  | Implicit.Empty -> Explicit.Empty (generate_metavar ())
  | Implicit.Cons (e1, e2) -> Explicit.Cons (add_metavars e1, add_metavars e2)
  | Implicit.Head e -> Explicit.Head (add_metavars e)
  | Implicit.Tail e -> Explicit.Tail (add_metavars e)
  | Implicit.IsEmpty e -> Explicit.IsEmpty (add_metavars e)
  | Implicit.Let (id, e1, e2) -> Explicit.Let (id, add_metavars e1, add_metavars e2)
  | Implicit.App (fn, arg) -> Explicit.App (add_metavars fn, add_metavars arg)
  | Implicit.Record r -> Explicit.Record (List.map (fun (k, v) -> (k, add_metavars v)) r)
  | Implicit.GetField (r, f) -> Explicit.GetField (add_metavars r, f)
  | Implicit.MkArray (e1, e2) -> Explicit.MkArray (add_metavars e1, add_metavars e2)
  | Implicit.GetArray (e1, e2) -> Explicit.GetArray (add_metavars e1, add_metavars e2)
  | Implicit.SetArray (e1, e2, e3) -> Explicit.SetArray (add_metavars e1, add_metavars e2, add_metavars e3)
  | _ -> failwith "we don't know how to add  metavars yet"

(* After this point, we are only working with the explicitly-typed syntax, so
   opening the module is unambiguous. *)

open Explicit

type constr = typ * typ

type env = (id * typ) list (* Other representations are possible too *)

let constraints : (constr list) ref = ref []

let add_constraint (lhs : typ) (rhs : typ) : unit =
  constraints := (lhs, rhs) :: !constraints

let rec cgen (env : env) (exp : exp) : typ = match exp with
  | Const (Int _) -> TInt
  | Const (Bool _) -> TBool
  | Op2 (op, e1, e2) -> (
    let t1 = (cgen env e1) in
    let t2 = (cgen env e2) in
    if op == Eq then
      match (t1, t2) with 
      | (TInt, _) -> 
          add_constraint t1 TInt;
          add_constraint t2 TInt;
      | (TBool, _) ->
          add_constraint t1 TBool;
          add_constraint t2 TBool;
      | (_, TBool) ->
          add_constraint t1 TBool;
          add_constraint t2 TBool;
      | (_, TInt) -> 
          add_constraint t1 TInt;
          add_constraint t2 TInt;
      | (TMetavar t3, TMetavar t4) -> add_constraint t1 t2;
      | _ -> failwith "equality is defined only on pairs of integers and booleans"
    else begin
      add_constraint t1 TInt;
      add_constraint t2 TInt;
    end;
    match op with 
    | LT -> TBool
    | GT -> TBool
    | Eq -> TBool
    | _ -> TInt
    )
  | If (e1, e2, e3) -> (
      let t2 = (cgen env e2) in
      add_constraint t2 (cgen env e3);
      add_constraint (cgen env e1) TBool;
      t2
    )
  | Empty t -> TList t
  | Cons (e1, e2) -> let t = cgen env e1 in 
      add_constraint (cgen env e2) (TList t);
      TList t
  | Head e -> (let t = (cgen env e) in
      add_constraint t (TList (generate_metavar ()));
      match t with 
      | TList t1 -> t1
      | TMetavar t1 -> let ht = generate_metavar () in
        add_constraint t (TList ht);
        ht
      | _ -> failwith "head should operate on a list"
    )
  | Tail e -> (let t = (cgen env e) in
      add_constraint t (TList (generate_metavar ()));
      match t with 
      | TList t -> TList t
      | TMetavar t -> TMetavar t
      | _ -> failwith "tail should operate on a list"
    )
  | IsEmpty e -> (let t = (cgen env e) in
      add_constraint t (TList (generate_metavar ()));
      match t with
      | TList t -> TBool
      | TMetavar t -> TBool
      | _ -> failwith "is_empty should operate on a list"
    )
  | MkArray (e1, e2) ->
      add_constraint (cgen env e1) TInt;
      TArr (cgen env e2)
  | GetArray (e1, e2) ->  (
      let t = (cgen env e1) in
      add_constraint (cgen env e2) TInt;
      match t with
      | TArr t1 -> t1
      | TMetavar t1 -> 
          let t2 = generate_metavar () in
          add_constraint t (TArr t2);
          t2 
    )
  | SetArray (e1, e2, e3) -> (
      let t = (cgen env e1) in 
      let t_rhs = (cgen env e3) in
      add_constraint (cgen env e2) TInt;
      match t with 
      | TArr t1 -> 
          add_constraint t1 t_rhs;
          t1
      | TMetavar t1 ->
          let t2 = generate_metavar () in
          add_constraint t (TArr t2);
          add_constraint t_rhs t2;
          t2
    )
  | Let (id, e1, e2) -> cgen ((id, cgen env e1) :: env) e2
  | Fun (x, t1, e) ->
      let t2 = cgen ((x, t1) :: env) e in
      TFun (t1, t2)
  | Fix (x, t1, e) ->
      add_constraint t1 (cgen ((x, t1) :: env) e);
      t1
  | App (fn, arg) ->
      let arg_type = cgen env arg in
      let ret_type = generate_metavar () in
      add_constraint (cgen env fn) (TFun (arg_type, ret_type));
      ret_type
  | Record r -> TRecord (List.map (fun (k, v) -> (k, cgen env v)) r)
  | GetField (r, f) -> (
      let t = cgen env r in
      (* let _ = pp_typ Format.std_formatter t  in*)
      match t with
      | TRecord tlist -> List.assoc f tlist
      | TMetavar x ->
          let y = generate_metavar () in
          add_constraint t (TRecord [(f, y)]);
          y
      | _ -> failwith "cannot determine type of get_field"
    )
  | Id x -> List.assoc x env

module type SUBST = sig
  type t

  val empty : t
  val singleton : metavar -> typ -> t
  val apply : t -> typ -> typ
  val compose : t -> t -> t
  val to_list : t -> (metavar * typ) list (* for debugging *)
end


module Subst : SUBST = struct
  type t = (metavar * typ) list
  let empty = []
  let singleton x typ = (x, typ) :: empty
  let rec apply subst typ = (match typ with
    | TInt -> TInt
    | TBool -> TBool
    | TMetavar x -> if List.mem_assoc x subst then List.assoc x subst else typ
    | TFun (t1, t2) -> TFun (apply subst t1, apply subst t2)
    | TRecord t -> TRecord (List.map (fun (k, v) -> (k, apply subst v)) t)
    | TList t -> TList (apply subst t)
    | TArr t -> TArr (apply subst t)
    | _ ->
      let _ = pp_typ Format.std_formatter typ in
      failwith "we don't know how to apply this yet"
  )
  (* FIXME *)
  let compose subst1 subst2 = subst1 @ subst2
  let to_list subst = match subst with
    | [l] -> [l]
end

(* Some examples of operations on substitutions *)
let x : metavar = "__x"
let y : metavar = "__y"
let z : metavar = "__z"
                    
let%TEST "Subst.apply should replace x with TInt" =
  let s = Subst.singleton x TInt in
  Subst.apply s (TMetavar x) = TInt

let%TEST "Subst.apply should recur into type constructors" =
  let s = Subst.singleton x TInt in
  Subst.apply s (TFun (TMetavar x, TBool)) = (TFun (TInt, TBool))

let%TEST "Subst.compose should distribute over Subst.apply (1)" =
  let s1 = Subst.singleton x TInt in
  let s2 = Subst.singleton y TBool in
  Subst.apply (Subst.compose s1 s2) (TFun (TMetavar x, TMetavar y)) =
  Subst.apply s1 (Subst.apply s2 (TFun (TMetavar x, TMetavar y)))

let%TEST "Subst.compose should distribute over Subst.apply (2)" =
  let s1 = Subst.singleton x TBool in
  let s2 = Subst.singleton y (TMetavar x) in
  Subst.apply (Subst.compose s1 s2) (TFun (TMetavar x, TMetavar y)) =
  Subst.apply s1 (Subst.apply s2 (TFun (TMetavar x, TMetavar y)))

let occurs (t1: typ) (t2: typ): bool =
  match t2 with
  | TInt -> false
  | TBool -> false
  | TFun (t3, t4) -> t1 = t3 || t1 = t4
  | TList t -> t1 = t
  | TRecord t -> 
      let li = List.map (fun (k, v) -> t1 = v) t in
      List.fold_left (fun acc x -> acc || x) false li
  | TArr t -> t1 = t
  | TMetavar m -> t1 = t2

let rec unify (t1 : typ) (t2 : typ) : Subst.t =
  match (t1, t2) with
  | (TInt, TInt) -> Subst.empty
  | (TBool, TBool) -> Subst.empty
  | (TRecord l1, TRecord l2) -> (
      let li = List.map (fun (k, v) -> unify v (List.assoc k l1)) l2 in
      let rec build_subst (li: 'a list): Subst.t =
      match li with
      | [] -> Subst.empty
      | subst :: t ->  Subst.compose subst (build_subst t)
      in
      build_subst li
    )

  (* FIXME: occurs check *)
  | (TMetavar t, t2) -> if (occurs t1 t2) then failwith "occurs check failed" else Subst.singleton t t2
  | (t1, TMetavar t) -> if (occurs t2 t1) then failwith "occurs check failed" else Subst.singleton t t1
  | (TFun (t1, t2), TFun (t3, t4)) -> Subst.compose (unify t1 t3) (unify t2 t4)
  | (TList t1, TList t2) -> unify t1 t2
  | (TArr t1, TArr t2) -> unify t1 t2
  | _ ->
    let _ = printf "Type 1:" in
    let _ = pp_typ Format.std_formatter t1 in
    let _ = printf "\n\n" in
    let _ = printf "Type 2:" in
    let _ = pp_typ Format.std_formatter t2 in 
    failwith "we don't know how to unify this yet or unification failure"

(* An incomplete suite of tests for unification *)
let%TEST "unifying identical base types should return the empty substitution" =
  Subst.to_list (unify TInt TInt) = []

let%TEST "unifying distinct base types should fail" =
  try let _ = unify TInt TBool in false
  with Failure _ -> true

let%TEST "unifying with a variable should produce a singleton substitution" =
  Subst.to_list (unify TInt (TMetavar x)) = [(x, TInt)]

let%TEST "unification should recur into type constructors" =
  Subst.to_list (unify (TFun (TInt, TInt))
                       (TFun (TMetavar x, TInt))) =
  [(x, TInt)]

let%TEST "unification failures may occur across recursive cases" =
  try
    let _ = unify (TFun (TInt, TMetavar x))
                  (TFun (TMetavar x, TBool)) in
    false
  with Failure _ -> true

let%TEST "unification should produce a substitution that is transitively closed" =
  let subst = unify (TFun (TFun (TInt, TMetavar x), TMetavar y))
                    (TFun (TFun (TMetavar x, TMetavar y), TMetavar z)) in
  Subst.to_list subst = [ (z, TInt); (y, TInt); (x, TInt) ]

let%TEST "unification should detect constraint violations that require transitive
      closure" =
  try
    let _ = unify (TFun (TFun (TInt, TMetavar x), TMetavar y))
                      (TFun (TFun (TMetavar x, TMetavar y), TBool)) in
    false
  with Failure _ -> true

let%TEST "unification should implement the occurs check (to avoid infinite loops)" =
  try
    let _ = unify (TFun (TInt, TMetavar x)) (TMetavar x) in
    false (* a bug is likely to cause an infinite loop *)
  with Failure _ -> true

let annotate_exp (subst : Subst.t) (exp : exp) : exp = failwith "not implemented"

let rec unify_and_apply (constraints: 'a list): unit =
  match constraints with
  | []  -> ()
  | h :: t -> 
      let (t1, t2) = h in
      let s = unify t1 t2 in
      unify_and_apply (List.map (fun (tx, ty) -> (Subst.apply s tx, Subst.apply s ty)) t)

let typeinf (exp : Implicit.exp) : Explicit.exp =
  let exp = add_metavars exp in
  let _ = cgen [] exp in
  let _ = unify_and_apply !constraints in
  exp
                                       
let _ =
  let filename : string = Sys.argv.(1) in
  let program : Implicit.exp = Implicit.from_file filename in
  pp_exp Format.std_formatter (typeinf program)
  (* typeinf program*)
