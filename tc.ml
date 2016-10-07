(* To compile this file, run:
 *
 * ocamlbuild -use-ocamlfind -pkg compsci631 -pkg ppx_test tc.d.byte
 *
 * This produces an executable called tc.d.byte.
 *)
open Tc_util
open Printf

let ty (c: const): typ = 
  match c with 
  | Int n -> TInt
  | Bool b -> TBool
  | _ -> failwith "not a constant"

let is_valid_int (t: typ): bool = 
  match t with 
  | TInt -> true
  (* | TId id -> true*)
  | _ -> false

let is_valid_bool (t: typ): bool = 
  match t with 
  | TBool -> true
  (* | TId id -> true*)
  | _ -> false

let delta (op2: op2) (t1: typ) (t2: typ): typ =
  if op2 == Eq then
    match (t1, t2) with 
    | (TInt, TInt) -> TBool
    | (TBool, TBool) -> TBool
    | _ -> failwith "equality is defined only on pairs of integers and booleans"
  else
    if (is_valid_int t1) == false  || (is_valid_int t2) == false then
      failwith "both the operands have to be of type int"
    else
      match op2 with
      | LT -> TBool
      | GT -> TBool
      | Add -> TInt
      | Sub -> TInt
      | Mul -> TInt
      | Div -> TInt
      | Mod -> TInt
      | _ -> failwith "unknown binary operation"

let resolve (t: typ) (tenv: 'a list): typ =
  match t with
  | TId id -> if List.mem_assoc id tenv then t else failwith "unresolved generic"
  | t -> t

let rec replace (tid: tid) (t2: typ) (t1: typ): typ =
  (* let _ = pp_typ Format.std_formatter t1 in*)
  match t1 with
  | TInt -> TInt
  | TBool -> TBool
  | TId tid -> t2
  | TFun (t3, t4) -> TFun ((replace tid t2 t3), (replace tid t2 t4))
  | TList t -> TList (replace tid t2 t)
  | TRecord t -> TRecord (List.map (fun (key, value) -> (key, (replace tid t2 value))) t)
  | TArr t -> TArr (replace tid t2 t)
  | TForall (tid2, t) -> TForall (tid2, replace tid t2 t)
  | _ -> failwith "do not know how to replace yet"

let rec equal (t1: typ) (t2: typ): bool =
  (* let _ = pp_typ Format.std_formatter t1 in*)
  (* let _ = pp_typ Format.std_formatter t2 in*)
  match (t1, t2) with
  | (TInt, TInt) -> true
  | (TBool, TBool) -> true
  | (TId id1, TId id2) -> id1 = id2
  | (TFun (t3, t4), TFun (t5, t6)) -> (equal t3 t5) && (equal t4 t6)
  | (TList t3, TList t4) -> equal t3 t4
  | (TRecord t3, TRecord t4) -> true
  | (TArr t3, TArr t4) -> equal t3 t4
  | (TForall (tid3, t3), TForall (tid4, t4)) -> (tid3 = tid4) && (equal t3 t4)
  | _ -> false

let rec check_type (e: exp) (env: 'a list) (tenv: 'a list): typ =
  let check e = check_type e env tenv in
  
  let get_list_type e = 
    match (check e) with 
    | TList t -> t
    | TId id -> TId id
    | _ -> failwith "expected a list"
  in

  match e with
  | Const c -> ty c
  | Op2 (op2, e1, e2) -> delta op2 (check e1) (check e2)
  | If (e1, e2, e3) -> (
      if (is_valid_bool (check e1)) then
        let t2 = check e2 in
        let t3 = check e3 in 
        match (t2, t3) with
        | (TId id2, TId id3) -> TId id2
        | (TId id2, t3) -> t3
        | (t2, TId id3) -> t2
        | (t2, t3) ->
            if (equal t2 t3) then
              t3
            else
              failwith "both if and else expressions should have the same type"
      else 
        failwith "conditional expression in if should be of type bool"
    )
  | Let (id, e1, e2) -> check_type e2 ((id, check e1) :: env) tenv
  | Fun (id, typ, e) -> (
      let ret = TFun (typ, (check_type e ((id, typ) :: env) tenv)) in
      match typ with
      | TId id ->
          if List.mem_assoc id tenv then
            ret
          else
            failwith "unknown generic type"
      | _ -> ret
    )
  | Fix (id, typ, e) -> (
      let ret = TFun (typ, (check_type e ((id, typ) :: env) tenv)) in
      match typ with
      | TId id ->
          if List.mem_assoc id tenv then
            ret
          else
            failwith "unknown generic type"
      | ret -> ret
      | _ -> failwith "fix should return an expression of the same type as its argument"
    )
  | App (e1, e2) -> (
      match (check e1) with
      | TFun (arg_typ, ret_typ) -> (
          match (arg_typ, (check e2)) with
          | (TId id1, TId id2) -> ret_typ
          | (TId id1, t) -> ret_typ
          | (t, TId id2) -> ret_typ
          | (t1, t2) ->
            if (equal t1 t2) then
              ret_typ
            else
              failwith "argument to function is not of the type that it expects"
        )
      | TId id -> TId id
      (* | TInt -> *)
          (* let _ = printf "Here\n" in*)
          (* let _ = pp_exp Format.std_formatter e1 in*)
          (* let _ = pp_typ Format.std_formatter (check e1) in*)
          (* failwith "how are we getting int"*)
      | _ -> failwith "LHS of function application should have type function"
    )
  | Id id -> List.assoc id env
  | Empty typ -> (
      match typ with
      | TId id ->
          if List.mem_assoc id tenv then
            TList typ
          else
            failwith "unknown generic type"
      | _ -> TList typ
    )
  | Cons (e1, e2) -> (
      let typ = get_list_type e2 in
      match ((check e1), typ) with
      | (TId id1, TId id2) -> TList typ
      | (TId id1, t) -> TList typ
      | (t, TId id2) -> TList typ
      | (t1, t2) ->
          if (equal t1 t2) then 
            (TList typ)
          else
            failwith "lists must be homogenous"
    )
  | Head e -> get_list_type e
  | Tail e -> TList (get_list_type e)
  | IsEmpty e -> let typ = get_list_type e in TBool
  | Record e -> TRecord (List.map (fun (key, value) -> (key, check value)) e)
  | GetField (r, f) -> (
      match (check r) with
      | TRecord typ_rec -> List.assoc f typ_rec
      | TId id -> TId "record_field"
      | _ -> failwith "LHS of get field operation should be a record"
    )
  | MkArray (l, d) -> (
      let t1 = (check l) in 
      let t2 = (check d) in
      (* match (t1, t2) with*)
      (* | (TId id1, TId id2) -> TArr t2*)
      (* | (TId id1, t) -> TArr t2*)
      (* | (t, TId id2) -> TArr t2*)
      (* | (t1, t2) ->*)
      if t1 != TInt then
        failwith "length argument to make array should be of type int"
      else
        TArr t2
    )
  | GetArray (e1, e2) -> (
      match (check e1) with 
      | TArr t ->
          if (equal (check e2) TInt) then
            t
          else
            failwith "array index should be of type int"
      | TId id ->  failwith "coming soon"
      | _ -> failwith "LHS of getarray should be of type array"
    )
  | SetArray (e1, e2, e3) -> (
      match (check e1) with
      | TArr t ->
          if (equal (check e2) TInt) then
            if (equal (check e3) t) then
              t
            else
              failwith "arrays should be homogenous"
          else
            failwith "array index should be of type int"
      | TId id -> failwith "coming soon"
      | _ -> failwith "LHS of setarray should be of type array"
    )
  | TypFun (tid, e) -> 
      let t = check_type e env ((tid, TId tid) :: tenv) in
      TForall (tid, t)
  | TypApp (e, typ) ->
    match (check e) with
    | TForall (tid, t1) -> 
        (* let _ = pp_typ Format.std_formatter typ in*)
        let t2 = resolve typ tenv in
        replace tid t2 t1
    | _ -> failwith "LHS of type function application should be a type function"
  | _ -> failwith "not implemented"


let _ =
  let filename : string = Sys.argv.(1) in
  let program : exp = from_file filename in
  (* let _ = pp_exp Format.std_formatter program in*)
  (* let _ = printf "\n\n" in*)
  let res = check_type program [] [] in
  let _ = pp_typ Format.std_formatter res in
  printf "\n\n"
