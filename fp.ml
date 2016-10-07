(* To compile this file, run:
 *
 * ocamlbuild -use-ocamlfind -pkg compsci631 -pkg ppx_test fp.d.byte
 *
 * This produces an executable called ./fp.d.byte, which runs all the
 * test cases in the file.
 *
 * If you've renamed the file to say foo.ml, you can instead run:
 *
 * ocamlbuild -use-ocamlfind -pkg compsci631 -pkg ppx_test foo.d.byte
 *)

(* This is necessary for let%TEST to work. *)
module PTest = Ppx_test.Test
open Printf

(* Do not change this definition *)
let rec foldr (f : 'a -> 'b -> 'b) (acc: 'b) (lst : 'a list) : 'b =
  match lst with
  | [] -> acc
  | hd :: tl -> f hd (foldr f acc tl)

(* Do not change this definition *)
let rec unfold (p : 'b -> bool) (g : 'b -> 'a * 'b) (acc : 'b) : 'a list =
  match p acc with
    | true -> []
    | false ->
      let (a, acc') = g acc in
      a :: (unfold p g acc')

let length (lst : 'a list) : int =
  foldr (fun x y -> 1 + y) 0 lst

let filter (pred : 'a -> bool) (lst : 'a list) : 'a list =
  foldr (fun x y -> if pred x then x :: y else y) [] lst

let build_list (f : int -> 'a) (len : int) : 'a list =
  unfold (fun x -> x = 0) (fun x -> (f (len - x), x - 1)) len

let is_empty (lst : 'a list) : bool = 
  foldr (fun x y -> false) true lst

let zip (lst1 : 'a list) (lst2 : 'b list) : ('a * 'b) list =
  let zip_predicate (lst1, lst2) = 
    match (lst1, lst2) with 
      | ([], []) -> true
      | (lst1, []) -> true
      | ([], lst2) -> true
      | (lst1, lst2) -> false
  in
  let zip_generator (hd1::tl1, hd2::tl2) = (hd1, hd2), (tl1, tl2) in
  unfold zip_predicate zip_generator (lst1, lst2)

let map_using_unfold (f : 'a -> 'b) (lst : 'a list) : 'b list =
  unfold (fun x -> x = []) (fun (hd::tl) -> f hd, tl) lst

let map_using_fold (f : 'a -> 'b) (lst : 'a list) : 'b list =
  foldr (fun x y -> (f x) :: y) [] lst

let factorial n =
  match n with 
    | 0 -> 1
    | 1 -> 1
    | n -> 
      let lst = unfold (fun x -> x = 1) (fun x -> x, x - 1) n in 
      foldr (fun x y -> x * y) 1 lst

let insert (x : int) (lst : int list) : int list = 
  let prefix_lst = filter (fun y -> y <= x) lst in 
  let suffix_lst = filter (fun y -> y > x) lst in
  (* prefix_lst @ [x] @ suffix_lst *)
  foldr (fun y z -> y :: z) (x :: suffix_lst) prefix_lst

let insertion_sort (xs : int list) : int list =
  foldr (fun x y -> insert x y) [] xs

type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree

let same_in_order (tree1: 'a tree) (tree2: 'a tree): bool =
  let rec in_order (t: 'a tree ): 'a list = match t with
    | Leaf -> []
    | Node ( lhs , x , rhs ) -> in_order lhs @ x :: in_order rhs
  in

  let rec in_order_step tree lst =
    match tree with 
      | Leaf -> lst
      | Node (lhs, x, rhs) -> 
        let rem = in_order_step lhs lst in
        match rem with
          | [] -> []
          | head :: tail -> 
          if x = head then (in_order_step rhs tail) else rem
  in

  let first_list = in_order tree1 in 
  if (in_order_step tree2 first_list) = [] then true else false

let rec range (m: int) (n: int) (r: int list): int list = 
  if m = n then (r @ [n])
  else range (m + 1) n (r @ [m])

let rec from_to (m : int) (n: int) : int list = 
  range m n []

(* TESTS *)
let%TEST "length.1" = length([]) = 0
let%TEST "length.2" = length([1; 2; 3]) = 3

let%TEST "filter.1" = filter (fun x -> x >= 5) [] = []
let%TEST "filter.2" = filter (fun x -> x >=5) [1; 2; 5; 6; 7] = [5; 6; 7]

let%TEST "build_list.1" = build_list (fun x -> x * x) 5 = [0; 1; 4; 9; 16]

let%TEST "is_empty.1" = is_empty [] = true
let%TEST "is_empty.2" = is_empty [1; 2; 3] = false

let%TEST "zip.1" = zip [1; 3; 5] [2; 4; 6; 8] = [(1, 2); (3, 4); (5, 6)]

let%TEST "map_using_fold.1" = map_using_fold (fun x -> x * x) [2; 3; 4; 5] = [4; 9; 16; 25]
let%TEST "map_using_unfold.1" = map_using_unfold (fun x -> x * x) [2; 3; 4; 5] = [4; 9; 16; 25]

let%TEST "factorial.1" = factorial 5 = 120

let%TEST "insert.1" = insert 0 [] = [0]
let%TEST "insert.2" = insert 0 [1; 2; 3] = [0; 1; 2; 3]
let%TEST "insert.3" = insert 3 [1; 2; 4] = [1; 2; 3; 4]
let%TEST "insert.4" = insert 5 [1; 2; 4] = [1; 2; 4; 5]

let%TEST "insertion_sort.1" = insertion_sort [1; 3; 2; 7; 5] = [1; 2; 3; 5; 7]

let t1 = Node ( Node ( Leaf , 1, Leaf ), 2, Node ( Leaf , 3, Leaf ))
let t2 = Node ( Node ( Leaf , 100, Leaf ), 2, Node ( Leaf , 3, Leaf ))
let%TEST "same_in_order.1" = same_in_order t1 t1 = true
let%TEST "same_in_order.2" = same_in_order t1 t2 = false

let%TEST "from_to.1"  = from_to 1 5 = [1; 2; 3; 4; 5]

(* END TESTS *)

(* Runs all tests declared with let%TEST. This must be the last line
   in the file. *)
let _ = Ppx_test.Test.collect ()
