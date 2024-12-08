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
        else Mono(coeff1 + coeff2, degre1) :: aux t

      (* remove monome if coeff = null *)
      else if coeff1 = 0 then
        if coeff2 = 0 then aux t 
        else Mono(coeff2, degre2) :: aux t
      else if coeff2 = 0 then Mono(coeff1, degre1) :: aux t
      
      (* nothing to change *)
      else Mono (coeff1, degre1) :: Mono (coeff2, degre2) :: aux t
  in 
  aux (List.sort (fun (Mono (_, degre1)) (Mono (_, degre2)) -> compare degre1 degre2) p);;

(* Example polynomial *)
let poly = [Mono(3, 2); Mono(4, 1); Mono(2, 2); Mono(5, 0)] ;;
canonique poly;;

(* QS 1.3: Addition of two polynomials *)
let poly2 = [Mono(5, 2); Mono(8, 1); Mono(6, 2); Mono(3, 0)] ;;

let rec poly_add (p1: polynome) (p2: polynome) : polynome = 
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
(*

let poly_prod (p1:polynome) (p2:polynome) : polynome = 
  let rec aux (Mono (coeff1, degre1)) p acc =
    match p with
    | [] -> acc
    | Mono (coeff2, degre2) :: t -> 
        aux (Mono (coeff1, degre1)) t ((Mono (coeff1 * coeff2, degre1 + degre2)) :: acc)  (* Ajouter le résultat et continuer *)
  in
  let rec aux2 p1 p2 acc =
    match p1 with
    | [] -> acc
    | h :: t -> let new_acc = poly_add acc (aux h p2 []) in aux2 t p2 new_acc
  in canonique (aux2 p1 p2 []);;
*)

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

(*
let poly_prod (p1:polynome) (p2:polynome) : polynome = 
  
  let monome_prod Mono(c1, d1) (p:polynome) = 
    List.map (fun Mono(c2, d2) -> (c1 * c2, d1 + d2)) p 
      
  in (canonique (List.fold_left (fun acc mon -> poly_add acc (monome_prod mon p2)) [] p1));;
*)


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
  | h::t -> gen_arb (etiquetage h) :: transform_ABR t;;

(*let list_ABR = generer_n_ABR 200 20;;
let transformed_ABR_list = transform_ABR list_ABR;;*)

(* QS 2.14 *)
(* Méthode naïve : conversion de chaque arbre en polynome canonique p  uis les additionner *)

let add_n_tree_to_poly_naive l =
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

let add_n_tree_to_poly_fusion l = arb2poly (Add l);;

let add_n_tree_to_poly_divide l = 
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

let testNaiveExo14 = add_n_tree_to_poly_naive transformed_ABR_list2;;
let testFusionExo14 = add_n_tree_to_poly_fusion transformed_ABR_list2;; 
let testDivideExo14 = add_n_tree_to_poly_divide transformed_ABR_list2;;

(* Evaluate the execution time of a function *) 
let time f x =
  let start = Sys.time() in 
  let _ = f x in
  let stop = Sys.time() in 
  let duration = stop -. start in
  Printf.printf "Temps d'execution : %fs\n" duration;
  duration;;

let rec generate_trees n = 
  if n = 1000 then [transform_ABR (generer_n_ABR n 20)]
  else transform_ABR (generer_n_ABR n 20) :: generate_trees (n+100);; 
                                                      
(* Execute the tests with n = 100, ..., 1000 and store the execution time *)
let rec fullTest1 l = match l with
  | [] -> [] 
  | h::t -> time add_n_tree_to_poly_naive h :: fullTest1 t;;

let rec fullTest2 l = match l with
  | [] -> [] 
  | h::t -> time add_n_tree_to_poly_fusion h :: fullTest2 t;;

let rec fullTest3 l = match l with
  | [] -> [] 
  | h::t -> time add_n_tree_to_poly_divide h :: fullTest3 t;;

let fullTestList = generate_trees 100
let real1 = fullTest1 fullTestList
let real2 = fullTest2 fullTestList
let real3 = fullTest3 fullTestList
(* QS 2.15 *)

let prod_n_tree_to_poly_naive l =
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

let prod_n_tree_to_poly_fusion l = arb2poly (Mul l);;
(*
let prod_n_tree_to_poly_divide l = 
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
| _ -> let (left, right) = split trees in poly_prod (divide_and_conquer left) (divide_and_conquer right)
in divide_and_conquer l;;*)

let prod_n_tree_to_poly_divide l =
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

let testNaiveExo15 = prod_n_tree_to_poly_naive transformed_ABR_list2;;
let testFusionExo15 = prod_n_tree_to_poly_fusion transformed_ABR_list2;;
(*let testDivideExo15 = prod_n_tree_to_poly_divide transformed_ABR_list2;;*)

let rec fullTest4 l = match l with
  | [] -> [] 
  | h::t -> time prod_n_tree_to_poly_naive h :: fullTest4 t;;

let rec fullTest5 l = match l with
  | [] -> [] 
  | h::t -> time prod_n_tree_to_poly_fusion h :: fullTest5 t;;

let rec fullTest6 l = match l with
  | [] -> [] 
  | h::t -> time prod_n_tree_to_poly_divide h :: fullTest6 t;;


let real4 = fullTest4 fullTestList
let real5 = fullTest5 fullTestList
(*let real6 = fullTest6 fullTestList*)
(* QS 2.15 *)

(* QS 2.16*)

let generate_n_abr_v2 n = 
  let rec generate count prevSize = 
    if count = n then [] 
    else if (count = 0 || count = 1) then abr (gen_permutation 1) :: generate (count+1) 1
    else abr (gen_permutation (prevSize*2)) :: generate (count+1) (prevSize*2)
  in if n < 1 then [] else generate 0 1;;

let list_ABR3 = generate_n_abr_v2 15;;
let transformed_ABR_list3 = transform_ABR list_ABR3;; 

(* QS 2.17 & QS 2.18 : mêmes méthodes que 2.14 et 2.15 *) 

(*let fullTestList_v2a = transform_ABR (generate_n_abr_v2 7);;
let fullTestList_v2b = transform_ABR (generate_n_abr_v2 8);;
let fullTestList_v2c = transform_ABR (generate_n_abr_v2 9);;
let real1_v2a = time add_n_tree_to_poly_naive fullTestList_v2a;;
let real1_v2b = time add_n_tree_to_poly_naive fullTestList_v2b;;
let real1_v2c = time add_n_tree_to_poly_naive fullTestList_v2c;;
let real2_v2 = time add_n_tree_to_poly_fusion fullTestList_v2a;;
let real2_v2 = time add_n_tree_to_poly_fusion fullTestList_v2b;;
let real2_v2 = time add_n_tree_to_poly_fusion fullTestList_v2c;;
let real3_v2 = time add_n_tree_to_poly_divide fullTestList_v2a;;
let real3_v2 = time add_n_tree_to_poly_divide fullTestList_v2b;;
let real3_v2 = time add_n_tree_to_poly_divide fullTestList_v2c;;
let real4_v2 = time prod_n_tree_to_poly_naive fullTestList_v2a;;
let real5_v2 = time prod_n_tree_to_poly_fusion fullTestList_v2a;;
let real6_v2 = time prod_n_tree_to_poly_divide fullTestList_v2a;;*)
(*(*Karatsuba*)
(* Multiplie le polynome poly par n  *)
let multn poly n =
  let rec aux poly tmp =
    match poly with
    | [] -> List.rev tmp
    | Mono(a, b) :: t -> aux t (Mono(a * n, b) :: tmp)
  in aux poly [];;

(* Exponentiate the degree of each term in the polynomial *)
let multExpo poly n = 
  let rec aux poly tmp = 
    match poly with
    | [] -> List.rev tmp
    | Mono(a,b) :: t -> aux t (Mono(a, b + n) :: tmp)
  in aux poly [];;

(* retrieves highest degree in poly*)
let degre poly = 
  let sorted = List.rev (  poly) in
  match sorted with
  | [] -> -1           (* If the list is empty, return None *)
  | Mono(_, b) :: _ -> b;;  (* Get the highest degree (b) from the first element *)

(* Helper function to split a polynomial into two halves *) 
(*
let split_poly poly k =
  let rec aux left right = function
    | [] -> (List.rev left, List.rev right)  (* When the input list is empty, return the reversed left and right parts *)
    | Mono(a, b) :: t ->  (* For each monomial, check its degree b *)
        if b < k then     (* If the degree is less than k, add it to the left part *)
          aux (Mono(a,b) :: left) right t
        else              (* If the degree is greater or equal to k, add it to the right part *)
          aux left (Mono(a,b) :: right) t
  in aux [] [] poly  (* Start the recursion with two empty lists (left and right) *)
*)
(* Helper function to split a polynomial into two halves based on number of terms *)
let split_poly poly k =
  let rec aux left right n = function
    | [] -> (List.rev left, List.rev right)  (* Return the reversed left and right parts when done *)
    | Mono(a, b) :: t when n < k -> aux (Mono(a, b) :: left) right (n + 1) t
    | Mono(a, b) :: t -> aux left (Mono(a, b) :: right) (n + 1) t
  in
  aux [] [] 0 poly  (* Start the recursion with two empty lists and count from 0 *)

(* Karatsuba algorithm for multiplying polynomials *)
(*

let rec mult_karatsuba poly1 poly2 =
  (* Base case for empty polynomials (degree 0) *)
  if (degre poly1 = -1 || degre poly2 = -1 ) then 
    []
  else if (degre poly1 = 0 || degre poly2 = 0) then
    poly_prod poly1 poly2 (* Direct multiplication for degree 1 polynomials *)
  (* Base case for degree 1 polynomials (single monomial multiplication) *)
  else if (degre poly1 = 1 && degre poly2 = 1) then
    poly_prod poly1 poly2  (* Direct multiplication for degree 1 polynomials *)
  else
    let k = max (degre poly1) (degre poly2) in  (* Determine the degree *)
    let half = k / 2 in
    let (a0, a1) = split_poly poly1 half in
    let (b0, b1) = split_poly poly2 half in
    let c1 = mult_karatsuba a0 b0 in  (* Recursive multiplication for lower half *)
    let c2 = mult_karatsuba a1 b1 in  (* Recursive multiplication for upper half *)
    let c3 = poly_add a1 a0 in  (* Sum a1 + a0 *)
    let c4 = poly_add b1 b0 in  (* Sum b1 + b0 *)
    let u = mult_karatsuba c3 c4 in  (* Multiply the sums *)
    let c5 = poly_add (poly_add u (multn c2 (-1))) (multn c1 (-1)) in
    let c6 = multExpo c2 half in (* Shift the a1b1 result *)
    poly_add (poly_add c5 c6) c1;; (* Add all results together *)

*)

let rec mult_karatsuba poly1 poly2 =
  (* Helper: split a polynomial based on degree *)
  let split_poly poly k =
    List.partition (fun (Mono(_, deg)) -> deg < k) poly
  in

  (* Base cases *)
  if poly1 = [] || poly2 = [] then 
    []  (* One of the polynomials is zero *)
  else if List.length poly1 = 1 || List.length poly2 = 1 then 
    poly_prod poly1 poly2  (* Direct multiplication if either is a single term *)
  else
    (* Recursive case *)
    let deg1 = degre poly1 in
    let deg2 = degre poly2 in
    let k = max deg1 deg2 / 2 in
    let (a0, a1) = split_poly poly1 k in
    let (b0, b1) = split_poly poly2 k in

    (* Recursive multiplications *)
    let c1 = mult_karatsuba a0 b0 in  (* Low-degree terms *)
    let c2 = mult_karatsuba a1 b1 in  (* High-degree terms *)
    let mid = 
      mult_karatsuba (poly_add a0 a1) (poly_add b0 b1)
      |> poly_add (multn c1 (-1)) |> poly_add (multn c2 (-1))
    in

    (* Combine results *)
    let shifted_c2 = multExpo c2 (2 * k) in
    let shifted_mid = multExpo mid k in
    poly_add (poly_add c1 shifted_mid) shifted_c2;;


let prod_n_tree_to_poly_kaaratsuba l =
  let rec list2polyList treeList =
  match treeList with
  | [] -> []
  | h::t -> (arb2poly h) :: (list2polyList t)
  in
  let rec prodPolyList treeList =
  match treeList with
  | [] -> [Mono (1, 0)]
  | [h] -> h
  | h::t -> mult_karatsuba h (prodPolyList t)
  in prodPolyList (list2polyList l);;

let rec fullTest7 l = match l with
| [] -> [] 
| h::t -> time prod_n_tree_to_poly_kaaratsuba h :: fullTest6 t;;

let testKaaratsubaExo15 = prod_n_tree_to_poly_kaaratsuba transformed_ABR_list2;;

let real7 = fullTest7 fullTestList

let arb2poly_n exprs = 
  List.flatten (List.map arb2poly exprs);;
let rec fullTest707 l = match l with
| [] -> [] 
| h::t -> time mult_karatsuba h :: fullTest707 t;;

let k = generate_trees 100;;

let x = List.map arb2poly_n k;;
fullTest707 x;;*)