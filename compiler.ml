open Arm
open Printf
open Compiler_util

type value =
  | VInt of int
  | VBool of bool
  | VArray of value array
  | VClosure of id * (value list -> value)
  | VUnknown
  [@@deriving show]

let values = ref []
let var_counter = ref 0
let label_counter = ref 0
let regs = ref IdSet.empty
let free_regs = ref IdSet.empty
let backup_regs = [R1; R2; R3; R4; R5; R6; R7; R8; R9; R10; R11; R12; LR]
let fv = ref IdSet.empty
let fv_map = Hashtbl.create 4242
let base_expr_with_holes = (fun ae -> ERet ae)
let fn_aliases = ref []
let fn_arg_count = ref []
let _ = for i = 1 to 12 do regs := IdSet.add ("R" ^ (string_of_int i)) !regs done
let _ = for i = 1 to 12 do free_regs := IdSet.add ("R" ^ (string_of_int i)) !free_regs done

let add_value (id: id) (value: value) = 
  values := (id, value) :: !values

let add_alias (from: id) (to_: id) =
  let to_ = if List.mem_assoc to_ !fn_aliases then List.assoc to_ !fn_aliases else to_ in
  (* let _ = printf "From: %s\nTo: %s\n\n" from to_ in*)
  fn_aliases :=  (from, to_) :: !fn_aliases

let rec eval (e: exp): value =
  (* let _ = pp_exp Format.std_formatter e in*)
  (* let _ = printf "Length: %d" (List.length !values) in*)
  (* let _ = List.iter (fun (x, y) -> printf "%s" x) !values in*)
  let value = (
  match e with
  | Id id -> if List.mem_assoc id !values then List.assoc id !values else VUnknown
  | Const const -> (match const with
      | Int n -> VInt n
      | Bool b -> VBool b
    )
  | Op2 (op2, e1, e2) ->  (
      let v1 = eval e1 in
      let v2 = eval e2 in 
      match (v1, v2) with
      | (VInt n1, VInt n2) ->  (
          match op2 with
          | LT -> VBool (n1 < n2)
          | GT -> VBool (n1 > n2)
          | Eq -> VBool (n1 = n2)
          | Add -> VInt (n1 + n2)
          | Sub -> VInt (n1 - n2)
          | Mul -> VInt (n1 * n2)
          | Div -> VInt (n1 / (n2 + 1))
          | Mod -> VInt (n1 mod (n2 + 1))
        )
      | _ -> VUnknown
  )
  
  | If (e1, e2, e3) -> (
      let v2 = eval e2 in
      let v3 = eval e3 in
      match (eval e1) with 
      | VBool true -> v2
      | _ -> v3
  )
  | Let (id, e1, e2) ->
      let v = eval e1 in
      add_value id v;
      eval e2
  | Fun (name, params, body) -> VClosure (name, fun (v: value list) -> (
      let rec build_list (params: id list) (v: value list) = (
        match (params, v) with 
        | ([], []) -> ()
        | (phd :: ptl, vhd :: vtl) -> add_value phd vhd; 
            build_list ptl vtl
        | _ -> ()
      ) in
      let _ = build_list params v in
      (* let _ = printf " Trying to eval body \n"  in*)
      let value = eval body in
      (* FIXME *)
      (* List.iter (fun param -> values := List.remove_assoc param !values) params;*)
      value
    ))
  | App (fn, args) -> (
      let arg_list = ref [] in
      let v = (eval fn) in
      let _ = List.iter (fun arg -> arg_list := (eval arg) :: !arg_list ) args in
      match (fn, v) with
      | (Id fid, VClosure (id, closure)) -> 
          if fid = id then v else closure !arg_list
      | (_, VClosure (id, closure)) -> closure !arg_list
      | _ -> VUnknown
    )
  | MkArray (length, default) -> (
      let vl = eval length in
      let vd = eval default in
      match vl with
      | VInt n -> VArray (Array.make n vd)
      | _ -> VUnknown
    )
  | GetArray (arr, index) -> (
      let v1 = eval arr in
      let v2 = eval index in
      match (v1, v2) with
      | (VArray a, VInt n) -> if n >= Array.length a then VUnknown else a.(n)
      | _ -> VUnknown
    )
  | SetArray (arr, index, value) -> (
      let v1 = eval arr in
      let v2 = eval index in
      let v3 = eval value in
      match (v1, v2) with
      | (VArray a, VInt n) -> if n >= Array.length a then VUnknown else let _ = a.(n) <- v3 in  v3
      | _ -> VUnknown
  )) in
  (* let _ = pp_value Format.std_formatter value in*)
  value
  (* | Seq of exp * exp *)
  

let gen_var (): id =
  let _ = incr var_counter in
  (string_of_int !var_counter)

let gen_label (): string = 
  let _ = incr label_counter in
  ("label" ^ string_of_int !label_counter)

let get_reg (): string = 
  let reg = IdSet.choose !free_regs in
  let _ = free_regs := IdSet.remove reg !free_regs in
  (* let _ = printf "Chosen: %s\n" reg in*)
  reg

let rec get_operand (e: aexp): operand =
  match e with
  | AConst (Int n) -> Imm n
  | AConst (Bool b) -> if b then (Imm 1) else (Imm 0)
  | AId id -> Reg (string_to_reg id)
  | _ -> failwith "atomize: not implemented"

let rec get_reg_from_aexp (e: aexp): reg =
  match e with
  | AId id -> string_to_reg id
  | _ -> failwith "get_reg_from_aexp: unexpected input"

let get_id (e: aexp): id = 
  match e with 
  | AId id -> id
  | _ -> "Invalid id"

let save_state (): assembly = 
  let cmds = ref [] in
  let _ = List.iter (fun reg -> cmds := push (Reg reg) :: !cmds) backup_regs in
  concat !cmds

let restore_state (): assembly =
  let cmds = ref [] in
  let _ = List.iter (fun reg -> cmds := pop reg :: !cmds) backup_regs in
  concat (List.rev !cmds)

let rec anf (e: exp) (expr_with_holes: (aexp -> anfexp)) : anfexp =
  let value = eval e in
  match e with
  | Const (Int n) -> expr_with_holes (AConst (Int n))
  | Const (Bool b) -> expr_with_holes (AConst (Bool b))
  | Id id -> expr_with_holes (AId id)
  | Op2 (op2, e1, e2) -> anf e1 (fun laexp -> anf e2 (fun raexp ->
      let id = gen_var () in
      add_value id value;
      ELet (id, BOp2 (op2, laexp, raexp), expr_with_holes (AId id))))
  | If (e1, e2, e3) -> anf e1 (fun caexp -> anf e2 (fun taexp -> anf e3 (fun faexp ->
      EIf (caexp, expr_with_holes taexp, expr_with_holes faexp))))
  | Let (id, e1, e2) -> anf e1 (fun vaexp -> ELet (id, BAtom vaexp, anf e2 expr_with_holes))
  | Fun (name, params, body) ->
      let id = gen_var () in
      add_value id value;
      (* let _ = (match value with*)
        (* | VClosure (fid, closure) -> add_value id (VClosure (id, closure));*)
      (* ) in*)
      (* FIXME: should body be passed expr_with_holes *)
      add_alias name id;
      add_alias id id;
      fn_arg_count :=  (id, List.length params) :: !fn_arg_count;
      ELet (id, BFun (name, params, anf body base_expr_with_holes), expr_with_holes (AId id))
      (* ELet (id, BFun (name, params, ERet (AId id)), expr_with_holes (AId id))*)
  | App (fn, args) -> anf fn (fun faexp ->
      let rec arganf (args: exp list) (anfargs: aexp list): anfexp = 
        match args with
        | [] -> 
            let id = gen_var () in
            add_value id value;
            ELet(id, BApp (faexp, List.rev anfargs), expr_with_holes (AId id))
        | hd :: tl -> anf hd (fun aaexp -> arganf tl (aaexp :: anfargs))
      in
      arganf args []
    )
  | MkArray (lexp, dexp) -> anf lexp (fun laexp -> anf dexp (fun daexp -> 
      let id = gen_var () in
      add_value id value;
      ELet (id, BMkArray (laexp, daexp), expr_with_holes (AId id))))
  | GetArray (aexp, iexp) -> anf aexp (fun aaexp -> anf iexp (fun iaexp ->
      let id = gen_var () in
      add_value id value;
      ELet (id, BGetArray (aaexp, iaexp), expr_with_holes (AId id))))
  | SetArray (aexp, iexp, vexp) -> anf aexp (fun aaexp -> anf iexp (fun iaexp -> anf vexp (fun vaexp ->
      let id = gen_var () in
      add_value id value;
      ELet (id, BSetArray (aaexp, iaexp, vaexp), expr_with_holes (AId id)))))
  | _ -> failwith "anf: not implemented"

let rec scan (reg: id) (e: anfexp): bool =
  match e with
  | ELet (id, bexp, e') -> (
      let t = (match bexp with
      | BFun (name, params, body) -> scan reg body
      | BAtom aexp -> if (get_id aexp) = reg then true else false
      | BOp2 (op2, laexp, raexp) -> if (get_id laexp) = reg then true else if (get_id raexp) = reg then true else false
      | BMkArray (vaexp, daexp) -> if (get_id vaexp) = reg then true else if (get_id daexp) = reg then true else false
      | BGetArray (aaexp, iaexp) -> if (get_id aaexp) = reg then true else if (get_id iaexp) = reg then true else false
      | BSetArray (aaexp, iaexp, vaexp) -> if (get_id aaexp) = reg then true else if (get_id iaexp) = reg then true else false
      | _ -> false
    ) in t || scan reg e'
  )
  | EIf (aexp, texp, fexp) -> if (get_id aexp) = reg then true  else scan reg texp || scan reg fexp
  | EApp (fn, args) -> if (get_id fn) = reg then true else 
      let li = List.filter (fun arg -> (get_id arg) = reg) args in if (List.length li) > 0 then true else false
  | ERet aexp -> if (get_id aexp) = reg then true else false
  | _ -> failwith "scan: not implemented"

let scan_and_free (e: anfexp) =
  let used_regs = IdSet.diff !regs !free_regs in
  IdSet.iter (fun reg -> if scan reg e then () else free_regs := IdSet.add reg !free_regs) used_regs

let rec allocate_registers (e: anfexp): anfexp =
  (* let _ = scan_and_free e in*)
  match e with
  | ELet (id, bexp, e') -> (
      match bexp with
      | BFun (name, params, body) ->
          let reg = get_reg () in
          let _ = fv := IdSet.diff (free_vars body) (IdSet.of_list params) in
          let n_free = IdSet.cardinal !fv in
          (* let _ = printf "Allocate: Label: %s\nn_fv: %d\n" id n_free in*)
          let _ = for i = 1 to n_free do
            let to_ = "R" ^ (string_of_int i) in
            let from = IdSet.choose !fv in
            let _ = fv := IdSet.remove from !fv in
            Hashtbl.add fv_map id (to_, from)
          done in

          let rec rename_params (params: id list) (index: int) (body: anfexp): anfexp = (
            match params with
            | [] -> body
            | hd :: tl -> 
                let reg = "R" ^ (string_of_int index) in
                let _ = free_regs := IdSet.remove reg !free_regs in
                rename_params tl (index + 1) (rename hd reg body)
          ) in

          let rec rename_fv (li: 'a list) (body: anfexp): anfexp = (
            match li with
            | [] -> body
            | (to_, from) :: tl -> rename_fv tl (rename from to_ body)
          ) in

          let backup_free_regs = !free_regs in
          let _ = free_regs := IdSet.empty in
          let _ = for i = (n_free + 1) to 12 do free_regs := IdSet.add ("R" ^ (string_of_int i)) !free_regs done in
          let body' = rename_fv (Hashtbl.find_all fv_map id) body in
          let body' = allocate_registers (rename_params params (n_free + 1) body') in
          let body' = rename name reg body' in
          let _ = free_regs := IdSet.empty in
          let _ = IdSet.iter (fun r -> free_regs := IdSet.add r !free_regs) backup_free_regs in
          let e' = rename id reg e' in
          add_alias reg id;
          ELet (reg, BFun (name, params, body'), (allocate_registers e'))
      | BApp (fn, args) ->
          let reg = get_reg () in
          let e' = rename id reg e' in
          let value = List.assoc id !values in
          let _ = (match value with
            | VClosure (fid, closure) -> add_alias reg fid;
            | _ -> ()
          ) in
          add_alias reg id;
          ELet (reg, bexp, (allocate_registers e'))
      | _ ->
          let reg = get_reg () in
          let e' = rename id reg e' in
          let value = List.assoc id !values in
          let _ = pp_value Format.std_formatter value in
          let _ = (match value with
            | VClosure (fid, closure) -> add_alias reg fid;
            | _ -> add_alias reg id
          ) in
          (* add_alias reg id;*)
          ELet (reg, bexp, (allocate_registers e'))
  )
  | EIf (aexp, texp, fexp) -> EIf (aexp, allocate_registers texp, allocate_registers fexp)
  | EApp (fn, args) ->  EApp (fn, args)
  | ERet aexp -> e
  | _ -> failwith "allocate: not implemented"

let div (op: string) (dst: reg) (src1: operand) (src2: operand): assembly =
  let euclid_div (r: reg) (src1: operand) (src2: operand): assembly =
      let in_label = gen_label() in
      let out_label = gen_label () in
      concat [
        cmp src2 (Imm 0);
        b ~cond:EQ "ez_abort";
        if op = "/" then mov dst (Imm 0) else mov dst src1;
        label in_label;
        cmp src1 src2;
        b ~cond:LT out_label;
        sub r src1 src2;
        if op = "/" then add dst (Reg dst) (Imm 1) else mov dst src1;
        b in_label;
        label out_label
      ]
  in
  match (src1, src2) with
  | (Imm x, Imm y) -> if y = 0 then b "ez_abort" else let value = if op = "/" then x / y else x mod y in mov dst (Imm (value))
  | (Reg r, _) -> euclid_div r src1 src2
  | (Imm _, Reg r) -> let reg_s1 = (string_to_reg (get_reg ())) in seq (mov reg_s1 src1) (euclid_div reg_s1 (Reg reg_s1) src2)

let compare (cond: cond) (dst: reg) (src1: operand) (src2: operand): assembly =
   concat [
      mov dst src1;
      cmp (Reg dst) src2;
      mov dst (Imm 0);
      mov dst (Imm 1) ~cond:cond
   ]

let my_mul (dst: reg) (src1: operand) (src2: operand): assembly =
  match (src1, src2) with
  | (Imm x, Imm y) -> mul dst src1 src2
  | (Reg r1, Reg r2) -> mul dst src1 src2
  | (Imm x, Reg y) ->
      let reg = string_to_reg (get_reg ()) in concat [mov reg src1; mul dst (Reg reg) src2]
  | (Reg x, Imm y) ->
      let reg = string_to_reg (get_reg ()) in concat [mov reg src2; mul dst src1 (Reg reg)]

let rec compile (e: anfexp): assembly =
  (* let _ = pp_anfexp Format.std_formatter e in*)
  try
    match e with
    | ELet (id, bexp, e') ->
        let reg = string_to_reg id in
        let asm = (
          match bexp with
          | BOp2 (op2, e1, e2) -> (
              let o1 = get_operand e1 in
              let o2 = get_operand e2 in
              match op2 with
              | Add -> add reg o1 o2
              | Sub -> sub reg o1 o2
              | Mul -> my_mul reg o1 o2
              | Div -> div "/" reg o1 o2
              | Mod -> div "%" reg o1 o2
              | LT -> compare LT reg o1 o2
              | GT -> compare GT reg o1 o2
              | Eq -> compare EQ reg o1 o2
              | _ -> failwith "unknown op2"
            )
          | BAtom aexp -> (
              match aexp with
              | AId id' ->
                  if List.mem_assoc id' !fn_aliases then
                    let _ = add_alias id (List.assoc id' !fn_aliases) in
                    mov reg (get_operand aexp)
                  else
                    (* let _ = printf "Nothing found for %s\n"  id' in*)
                    mov reg (get_operand aexp)
              | _ -> mov reg (get_operand aexp)
            )
          | BFun (name, params, body) -> 
              let fn_id = List.assoc id !fn_aliases in
              let fv = Hashtbl.find_all fv_map fn_id in
              let n_fv = List.length fv in
              let n_bytes = n_fv * 4 + 4 in
              let fv_cmds = ref [] in
              let _ = for i = 1 to n_fv do
                let to_ = "R" ^ (string_of_int i) in
                let from = List.assoc to_ fv in
                let from = if name = from then R0 else string_to_reg (List.assoc to_ fv) in
                fv_cmds := str (Reg from) R0 ~index:(ix (Imm (i * 4))) :: !fv_cmds
              done in
              let out_label = gen_label () in
              let fn_label = ("fn_" ^ fn_id) in
              concat [
                b out_label;
                label fn_label;
                push (Reg LR);
                compile body;
                pop PC;
                label out_label;
                adr reg fn_label;
                save_state ();
                push (Reg LR);
                mov R0 (Imm n_bytes);
                push (Reg R0);
                bl "ez_alloc";
                pop R0;
                pop LR;
                restore_state ();
                str (Reg reg) R0;
                mov reg (Reg R0);
                concat !fv_cmds;
              ]
              (* seq concat (compile e')) *)
          | BApp (fn, args) -> 
              let fn = get_id fn in
              (* let _ = printf "Trying to lookup %s\n" fn in*)
              if List.mem_assoc fn !fn_aliases then
                let label = List.assoc fn !fn_aliases in
                (* let _ = printf "Label: %s\n" label in*)
                let value = List.assoc label !values in
                let label = (match value with
                | VClosure (fid, closure) -> List.assoc fid !fn_aliases
                | _ -> label
                ) in
                (* let _ = pp_value Format.std_formatter (List.assoc label !values) in*)
                if List.mem_assoc label !fn_arg_count && List.assoc label !fn_arg_count != List.length args then
                  let _ = printf "ez_abort because wrong number of arguments\n" in
                  b "ez_abort"
               
                else
                  let fv = Hashtbl.find_all fv_map label in
                  let n_fv = List.length fv in
                  (* let _ = printf "Compile App: Label: %s\nn_fv: %d\n" label n_fv in*)
                  let fn_adr = string_to_reg fn in
                  let fv_cmds = ref [ldr R0 R0] in
                  let _ = for i = 1 to n_fv do 
                    let reg = string_to_reg ("R" ^ (string_of_int i)) in
                    fv_cmds := ldr reg R0 ~index:(ix (Imm (i * 4))) :: !fv_cmds
                  done in
                  let rec move_args_to_regs (args: aexp list) (index: int): assembly list = (
                    match args with
                    | [] -> []
                    | hd :: tl ->
                        let reg = "R" ^ (string_of_int index) in
                        let reg =  string_to_reg reg in
                        (mov reg (get_operand hd)) :: (move_args_to_regs tl (index + 1))
                  ) in
                  concat [
                    save_state ();
                    mov R0 (Reg fn_adr);
                    concat !fv_cmds;
                    concat (move_args_to_regs args (n_fv + 1));
                    mov LR (Reg PC);
                    bx R0;
                    (* bl ("fn_" ^ label);*)
                    restore_state ();
                    (*TODO: Deal with return value here *)
                    mov reg (Reg R0);
                  ]
              else
                let _ = printf "ez_abort because fn_alias not found for %s\n" fn in
                b "ez_abort"
          | BMkArray (length, default) -> concat [
              save_state ();
              mov R1 (get_operand default);
              mov R2 (get_operand length);
              bl "make_array";
              restore_state ();
              mov reg (Reg R0)
            ]
          | BGetArray (arr, index) -> 
              let ptr_arr = get_reg_from_aexp arr in
              let index = get_operand index in
              concat [
                ldr reg ptr_arr;
                cmp (Reg reg) index;
                b "ez_abort" ~cond:LE;
                add reg index (Imm 1);
                ldr reg ptr_arr ~index:(ix_lsl (Reg reg) 2)
              ]
          | BSetArray (arr, index, value) ->
              let ptr_arr = get_reg_from_aexp arr in
              let index = get_operand index in
              let value = get_operand value in
              let value_reg = string_to_reg (get_reg()) in
              concat [
                mov value_reg value;
                ldr reg ptr_arr;
                cmp (Reg reg) index;
                b "ez_abort" ~cond:LE;
                add reg index (Imm 1);
                str (Reg value_reg) ptr_arr ~index:(ix_lsl (Reg reg) 2);
                mov reg value
              ]
          | _ -> failwith "produce: not implemented"
        ) in
        seq asm (compile e')
    | EIf (cexp, texp, fexp) ->
        (* TODO: check for boolean here *)
        let o = get_operand cexp in
        let false_label = gen_label () in
        let out_label = gen_label () in
        concat [
          cmp o (Imm 0);
          b false_label ~cond:EQ;
          compile texp;
          b out_label;
          label false_label;
          compile fexp;
          label out_label;
        ]
      (* FIXME *)
    | EApp (fn, args) -> let reg = get_reg () in 
        compile (ELet (reg, BApp (fn, args), ERet (AId reg)))
    | ERet aexp -> mov R0 (get_operand aexp)
    | _ -> failwith "compile: not implemented"
  with _ -> b "ez_abort"

let _ =
  let filename : string = Sys.argv.(1) in
  let out_filename = Sys.argv.(2) in
  let program : exp = from_file filename in
  (* let _ = pp_exp Format.std_formatter program in*)
  (* let _ = pp_value Format.std_formatter (eval program) in*)
  let anf: anfexp = anf program base_expr_with_holes in
  (* let _ = pp_anfexp Format.std_formatter anf in*)
  let anf: anfexp = allocate_registers anf in
  (* let _ = pp_anfexp Format.std_formatter anf in*)
  let array_funcs = concat [
                      b "main_man";
                      label "make_array";
                      my_mul R0 (Reg R2) (Imm 4);
                      add R0 (Reg R0) (Imm 4); (* First element of array is size *)
                      push (Reg LR);
                      push (Reg R0);
                      bl "ez_alloc";
                      pop R0;
                      pop LR;
                      str (Reg R2) R0;
                      mov R3 (Imm 1);
                      label "populate_array";
                      cmp (Reg R2) (Reg R3);
                      bx LR ~cond:LT;
                      str (Reg R1) R0 ~index:(ix_lsl (Reg R3) 2);
                      add R3 (Reg R3) (Imm 1);
                      b "populate_array";
                      label "main_man"
                    ] in
  let asm : Arm.assembly = seq array_funcs (seq (compile anf) (bx LR)) in
  (* let asm : Arm.assembly = (seq (compile anf) (bx LR)) in*)
  let out_chan = open_out out_filename in
  (* let _ = printf "%s" (string_of_assembly asm) in*)
  output_string out_chan ".text\n.global ez_alloc\n.global ez_abort\n.global start\n.align 4\nstart:\n";
  output_string out_chan (Arm.string_of_assembly asm);
  close_out out_chan 
