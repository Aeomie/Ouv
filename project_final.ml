(* Part 1 *)
type monome = Mono of int * int;;
type polynome = monome list;;

(* QS 1.2 *) 
let canonique (p:polynome) : polynome =
  (* aux : take as argument a polynome sorted by degree and combine the monomes of same degree *)
  let rec aux p =
    match p with
    | [] -> []
    | [Mono (coeff, degre)] -> if coeff = 0 then [] else [Mono (coeff, degre)]
    | Mono (coeff1, degre1) :: Mono (coeff2, degre2) :: t ->
      if degre1 = degre2 then
        (* if sum of coeff is null -> remove both *)
        if (coeff1+coeff2) = 0 then aux t 
        (* else combine the monomes *)
        else aux (Mono(coeff1 + coeff2, degre1) :: t)

      (* remove monome if coeff = null *)
      else if coeff1 = 0 then aux (Mono(coeff2, degre2) :: t)
      else if coeff2 = 0 then aux (Mono(coeff1, degre1) :: t)
      (* nothing to change *)
      else Mono (coeff1, degre1) :: aux (Mono (coeff2, degre2) :: t)
  in 
  aux (List.sort (fun (Mono (_, degre1)) (Mono (_, degre2)) -> compare degre1 degre2) p);;

(* Example polynomial *)
let poly = [Mono(3, 2); Mono(4, 1); Mono(2, 2); Mono(5, 0)] ;;
canonique poly;;

(* QS 1.3: Addition of two polynomials *)
let poly2 = [Mono(5, 2); Mono(8, 1); Mono(6, 2); Mono(3, 0)] ;;

let poly_add (p1: polynome) (p2: polynome) : polynome = 
  let rec aux p1 p2 =
    match p1 with
    | [] -> p2
    | Mono(coeff1, degre1) :: t1 -> 
      match p2 with
      | [] -> p1
      | Mono(coeff2, degre2) :: t2 ->
        if degre1 = degre2 then 
          if (coeff1 + coeff2) = 0 then aux t1 t2 
          else Mono(coeff1 + coeff2, degre1) :: aux t1 t2
        else if degre1 < degre2 then 
          Mono(coeff1, degre1) :: aux t1 p2
        else 
          Mono(coeff2, degre2) :: aux p1 t2
  in aux p1 p2;;

(* Test the addition of two canonical polynomials *)
poly_add (canonique poly) (canonique poly2);;

(* QS 1.4: Multiplication of two polynomials *)

let poly_prod (p1:polynome) (p2:polynome) : polynome = 
  let rec aux (Mono (coeff1, degre1)) p =
    match p with
    | [] -> []
    | Mono (coeff2, degre2) :: t -> 
      Mono (coeff1 * coeff2, degre1 + degre2) :: aux (Mono (coeff1, degre1)) t (* Ajouter le résultat et continuer *)
  in
  let rec aux2 p1 p2 =
    match p1 with
    | [] -> []
    | h :: t -> poly_add (aux h p2) (aux2 t p2)
  in canonique (aux2 p1 p2);;

(* QS 1.5*)
type expr = 
  | Int of int
  | Var of string
  | Pow of expr list 
  | Add of expr list
  | Mul of expr list;; 

(*QS 1.6*)
let expr_tree =
  Add [
    Mul [Int 123; Pow [Var "x";Int 1]];
    Int 42;
    Pow [Var "x";Int 3]
  ];;
      
(* QS 1.7*)
let rec arb2poly expr_tree =
  match expr_tree with 
  | Int n -> [Mono(n, 0)]
  | Var x -> [Mono(1, 1)] 
  | Pow [base; Int n] -> if base = Var "x" then [Mono(1, n)] else failwith "only x as var"
  | Add children -> 
      let rec add_polys kids acc = 
        match kids with
        | [] -> acc
        | h :: t -> 
            let poly_hd = arb2poly h in  (* Convert the subtree into a polynomial *)
            add_polys t (poly_hd @ acc)  (* Add the polynomial to the list and recurse *)                                           
      in
      canonique (add_polys children [])
  | Mul children -> 
      let rec prod_polys kids = 
        match kids with
        | [] -> [Mono(1, 0)]
        | h :: t -> 
            let poly_hd = arb2poly h in  (* Convert the subtree into a polynomial *)
            poly_prod poly_hd (prod_polys t)  (* Add the polynomial to the list and recurse *)
      in
      prod_polys children
  | _ -> [];;
  
(* QS 1.8 *)

let extraction_alea list_L list_P =
  let rec remove_element n l = 
    match l with
    | [] -> []
    | h::t when n = 0 -> t
    | h::t -> h :: remove_element (n - 1) t
  in
  if List.length list_L = 0 
    then ([], list_P)
  else
    let random_int l = Random.int (List.length l) in 
    let r = random_int list_L in
    let elt = List.nth list_L r in 
    (remove_element r list_L, elt::list_P);;

let list1 = [1;2;3];;
let list2 = [5;6;7];;
extraction_alea list1 list2;;
  
(* QS 1.9 *)
let gen_permutation n =
  let rec generate_list upperBound count = match count with
    | _ when count = upperBound -> [count]
    | _ -> count :: generate_list upperBound (count+1)
  in
  let rec fill_list (l, p) = 
    if List.length l = 0 then p
    else fill_list (extraction_alea l p)
  in fill_list (generate_list n 1,[]);;

gen_permutation 10;; 

(* QS 1.10 *)

type 'a btree =
  | Empty
  | Node of 'a btree * 'a * 'a btree;;

let abr list = 
  let rec insertABR elt tree = 
    match tree with
    | Empty -> Node(Empty, elt, Empty)
    | Node (left, root, right) when elt < root -> Node(insertABR elt left, root, right)
    | Node (left, root, right) -> Node(left, root, insertABR elt right)
  in
  let rec buildABR l tree =
    match l with 
    | [] -> tree
    | h::t -> buildABR t (insertABR h tree)
  in buildABR list Empty;;

let list_permutation = gen_permutation 10;;
let abr_test = abr list_permutation;;

(* QS 1.11 *) 

let rec etiquetage tree =
  match tree with 
  | Node (Empty, root, Empty) -> 
    if (root mod 2) = 1 
      then Mul [Int ((Random.int 401) - 200); Var "x"] 
    else 
      Pow [Var "x"; Int (Random.int 101)] 
  | Empty -> 
    if Random.int 2 = 0 
      then Var "x" 
    else 
      Int (Random.int 101)
  | Node (left, root, right) -> 
    if (Random.int 4) <> 0 
      then Add [etiquetage left; etiquetage right] 
    else 
      Mul [etiquetage left; etiquetage right];; 
  
let etiq_test = etiquetage abr_test;; 

(* QS 1.12 *)

let rec gen_arb tree = 
  match tree with 
  | Int _ -> tree 
  | Var _ -> Pow [Var "x"; Int 1]
  | Pow [left; right] -> if right = (Int 0) then (Int 1) else Pow [left; right] (* right child is always the Int in the Pow node *)
  | Add [left; right] ->
      let rec addAux l r = 
        match l, r with
        | Add [subLeft1; subRight1], Add [subLeft2; subRight2] 
          -> Add [gen_arb subLeft1; gen_arb subRight1; gen_arb subLeft2; gen_arb subRight2]
        | Add [subLeft; subRight], _ -> Add [gen_arb subLeft; gen_arb subRight; gen_arb r]
        | _, Add [subLeft; subRight] -> Add [gen_arb l; gen_arb subLeft; gen_arb subRight] 
        | subLeft, subRight -> Add [gen_arb subLeft; gen_arb subRight] 
      in addAux left right
  | Mul [left; right] ->
      let rec mulAux l r = 
        match l, r with
        | Mul [subLeft1; subRight1], Mul [subLeft2; subRight2] 
          -> Mul [gen_arb subLeft1; gen_arb subRight1; gen_arb subLeft2; gen_arb subRight2]
        | Mul [subLeft; subRight], _ -> Mul [gen_arb subLeft; gen_arb subRight; gen_arb r]
        | _, Mul [subLeft; subRight] -> Mul [gen_arb l; gen_arb subLeft; gen_arb subRight] 
        | subLeft, subRight -> Mul [gen_arb subLeft; gen_arb subRight]
      in mulAux left right
  | _ -> failwith "unexpected case";; (* shouldn't happen when using a tree from etiquetage *)



let val_test9 =
  Add
    [Var "x";
     Add
       [Mul
          [Add [Int 34; Mul [Mul [Int (-5); Var "x"]; Mul [Int 80; Var "x"]]];
           Int 21];
        Mul [Var "x"; Add [Int 44; Pow [Var "x"; Int 69]]]]];;

let gen_arb_test = gen_arb val_test9;; 

let test9 = gen_arb etiq_test;;
      
(* Expérimentations *)                              
(* QS 2.13 *)

let rec generer_n_ABR n size = 
  if n = 0 then [] else abr (gen_permutation size) :: generer_n_ABR (n-1) size;;

let rec transform_ABR l = 
  match l with
  | [] -> []
  | [h] -> [gen_arb (etiquetage h)]
  | h::t -> gen_arb (etiquetage h) :: transform_ABR t;;

(*let list_ABR = generer_n_ABR 200 20;;
let transformed_ABR_list = transform_ABR list_ABR;;*)

(* QS 2.14 *)

(* Naive strategy : convert each tree into a polynomial and then add them together *)
let add_naive l =
  let rec list2polyList treeList =
    match treeList with
    | [] -> []
    | h::t -> (arb2poly h) :: (list2polyList t)
  in 
  let rec sumPolyList treeList =
    match treeList with
    | [] -> []
    | [h] -> h
    | h::t -> poly_add h (sumPolyList t)
  in sumPolyList (list2polyList l);;

(* Fusion strategy: create a new tree with a new Add node at the root that is linked to each tree 
   and convert this new tree to a polynomial *)
let add_fusion l = arb2poly (Add l);;

(* Divide and conquer strategy: split the problem into smaller subproblems, 
   solve them, and combine the results *)
let add_divide l = 
  let rec divide_and_conquer trees =
    let rec split lst =
      let rec aux l1 l2 count = 
        match l2 with
        | [] -> (List.rev l1, [])
        | h :: t -> 
            if count = 0 then (List.rev l1, l2)
            else aux (h :: l1) t (count - 1)
      in 
      aux [] lst (List.length lst / 2)
    in 
    match trees with
    | [] -> []
    | [h] -> arb2poly h
    | _ -> let (left, right) = split trees in poly_add (divide_and_conquer left) (divide_and_conquer right)
  in divide_and_conquer l;;
  
let list_ABR2 = generer_n_ABR 100 20;;
let transformed_ABR_list2 = transform_ABR list_ABR2;; 

let testNaiveExo14 = add_naive transformed_ABR_list2;;
let testFusionExo14 = add_fusion transformed_ABR_list2;; 
let testDivideExo14 = add_divide transformed_ABR_list2;;

(* Evaluate the execution time of a function *) 
let time f x =
  let start = Sys.time() in 
  let _ = f x in
  let stop = Sys.time() in 
  let duration = stop -. start in
  duration;;

let printTime f x =
  let start = Sys.time() in 
  let _ = f x in
  let stop = Sys.time() in 
  let duration = stop -. start in
  Printf.printf "Exec time : %fs\n" duration;
  duration;;

(* to generate a list containing n = 100, ... , n = 1000 *)
let rec generate_trees n = 
  if n >= 1000 then [transform_ABR (generer_n_ABR n 20)]
  else (transform_ABR (generer_n_ABR n 20)) :: generate_trees (n+100);; 
                            
(* Execute the tests with n = 100, ..., 1000 and store the execution time *)
let rec addNaiveTest l = match l with
  | [] -> [] 
  | h::t -> time add_naive h :: addNaiveTest t;;

let rec addFusionTest l = match l with
  | [] -> [] 
  | h::t -> time add_fusion h :: addFusionTest t;;

let rec addDivideTest l = match l with
  | [] -> [] 
  | h::t -> time add_divide h :: addDivideTest t;;

let treesQ14Q15 = generate_trees 10;;
let addNaiveDurationQ14 = addNaiveTest treesQ14Q15;;
let addFusionDurationQ14 = addFusionTest treesQ14Q15;;
let addDivideDurationQ14 = addDivideTest treesQ14Q15;;

(* QS 2.15 *)

(* Naive strategy : convert each tree into a polynomial and then multiply them together *)
let prod_naive l =
let rec list2polyList treeList =
match treeList with
| [] -> []
| h::t -> (arb2poly h) :: (list2polyList t)
in
let rec prodPolyList treeList =
match treeList with
| [] -> []
| [h] -> h
| h::t -> poly_prod h (prodPolyList t)
in prodPolyList (list2polyList l);;

(* Fusion strategy : same as the addition but with a Mul node *)
let prod_fusion l = arb2poly (Mul l);;

(* Divide and conquer strategy : same as the addition but with poly_prod *)
let prod_divide l =
  let rec divide_and_conquer lst left right =
    if right - left <= 1 then
      arb2poly (List.nth lst left)
    else
      let mid = (left + right) / 2 in
      poly_prod 
        (divide_and_conquer lst left mid)
        (divide_and_conquer lst mid right)
  in
  divide_and_conquer l 0 (List.length l)
;; 

(* Execute the tests with n = 100, ..., 1000 and store the execution time *)
let rec prodNaiveTest l = match l with
  | [] -> [] 
  | h::t -> time prod_naive h :: prodNaiveTest t;;

let rec prodFusionTest l = match l with
  | [] -> [] 
  | h::t -> time prod_fusion h :: prodFusionTest t;;

let rec prodDivideTest l = match l with
  | [] -> [] 
  | h::t -> time prod_divide h :: prodDivideTest t;;

let prodNaiveDurationQ15 = prodNaiveTest treesQ14Q15;;
let prodFusionDurationQ15 = prodFusionTest treesQ14Q15;;
let prodDivideDurationQ15 = prodDivideTest treesQ14Q15;;

(* Same tests *)
(*
let arb1 = transform_ABR (generer_n_ABR 100 20);;
let arb2 = transform_ABR (generer_n_ABR 200 20);;
let arb3 = transform_ABR (generer_n_ABR 300 20);;
let arb4 = transform_ABR (generer_n_ABR 400 20);;
let arb5 = transform_ABR (generer_n_ABR 500 20);;
let arb6 = transform_ABR (generer_n_ABR 600 20);;
let arb7 = transform_ABR (generer_n_ABR 700 20);;
let arb8 = transform_ABR (generer_n_ABR 800 20);;
let arb9 = transform_ABR (generer_n_ABR 900 20);;
let arb10 = transform_ABR (generer_n_ABR 1000 20);;

Printf.printf("Duration for prod naive\n");;
let timeProdNaive1 = printTime prod_naive arb1;;
let timeProdNaive2 = printTime prod_naive arb2;;
let timeProdNaive3 = printTime prod_naive arb3;;
let timeProdNaive4 = printTime prod_naive arb4;;
let timeProdNaive5 = printTime prod_naive arb5;;
let timeProdNaive6 = printTime prod_naive arb6;;
let timeProdNaive7 = printTime prod_naive arb7;;
let timeProdNaive8 = printTime prod_naive arb8;;
let timeProdNaive9 = printTime prod_naive arb9;;
let timeProdNaive10 = printTime prod_naive arb10;;

Printf.printf("Duration for prod fusion\n");;
let timeProdFusion1 = printTime prod_fusion arb1;;
let timeProdFusion2 = printTime prod_fusion arb2;;
let timeProdFusion3 = printTime prod_fusion arb3;;
let timeProdFusion4 = printTime prod_fusion arb4;;
let timeProdFusion5 = printTime prod_fusion arb5;;
let timeProdFusion6 = printTime prod_fusion arb6;;
let timeProdFusion7 = printTime prod_fusion arb7;;
let timeProdFusion8 = printTime prod_fusion arb8;;
let timeProdFusion9 = printTime prod_fusion arb9;;
let timeProdFusion10 = printTime prod_fusion arb10;;


Printf.printf("Duration for prod fusion\n");;
let timeProdDivide1 = printTime prod_divide arb1;;
let timeProdDivide2 = printTime prod_divide arb2;;
let timeProdDivide3 = printTime prod_divide arb3;;
let timeProdDivide4 = printTime prod_divide arb4;;
let timeProdDivide5 = printTime prod_divide arb5;;
let timeProdDivide6 = printTime prod_divide arb6;;
let timeProdDivide7 = printTime prod_divide arb7;;
let timeProdDivide8 = printTime prod_divide arb8;;
let timeProdDivide9 = printTime prod_divide arb9;;
let timeProdDivide10 = printTime prod_divide arb10;;

*)

(* QS 2.16*)

let generate_n_abr_v2 n = 
  let rec generate count prevSize = 
    if count = n then [] 
    else if (count = 0 || count = 1) then abr (gen_permutation 1) :: generate (count+1) 1
    else abr (gen_permutation (prevSize*2)) :: generate (count+1) (prevSize*2)
  in if n < 1 then [] else generate 0 1;;

(* QS 2.17 & QS 2.18 : mêmes méthodes que 2.14 et 2.15 *) 

let treesQ17Q18 = transform_ABR (generate_n_abr_v2 15);;

let addNaiveDurationQ17 = time add_naive treesQ17Q18;;
let addFusionDurationQ17 = time add_fusion treesQ17Q18;;
let addDivideDurationQ17 = time add_divide treesQ17Q18;;

let prodNaiveDurationQ18 = time prod_naive treesQ17Q18;;
let prodFusionDurationQ18 = time prod_fusion treesQ17Q18;;
let prodDivideDurationQ18 = time prod_divide treesQ17Q18;;

(* QS 2.19 *)
let averageTime iterations =
  let rec generate_tree count = 
    if count = 0 then [] 
    else (transform_ABR (generate_n_abr_v2 15)) :: generate_tree (count-1)
  in 
  let trees = generate_tree iterations in
  let rec aux f acc treeList =
    match treeList with
    | [] -> acc
    | h :: t ->
      let duration = time f h in
      aux f (acc +. duration) t
  in
  (* Call of each method *)
  let avg_naive = aux add_naive 0.0 trees /. float_of_int iterations in
  Printf.printf "Average time add naive : %fs\n" avg_naive;

  let avg_fusion = aux add_fusion 0.0 trees /. float_of_int iterations in
  Printf.printf "Average time add fusion : %fs\n" avg_fusion;

  let avg_divide = aux add_divide 0.0 trees /. float_of_int iterations in
  Printf.printf "Average time add divide : %fs\n" avg_divide;

  let avg_prod_naive = aux prod_naive 0.0 trees /. float_of_int iterations in
  Printf.printf "Average time prod naive : %fs\n" avg_prod_naive;

  let avg_prod_fusion = aux prod_fusion 0.0 trees /. float_of_int iterations in
  Printf.printf "Average time prod fusion : %fs\n" avg_prod_fusion;

  let avg_prod_divide = aux prod_divide 0.0 trees /. float_of_int iterations in
  Printf.printf "Average time prod divide : %fs\n" avg_prod_divide;
;;

averageTime 10;;