  (* Part 1 *)
  type monome = Mono of int * int;;
  type polynome = Poly of monome list;;

  (* QS 1.2 *) 

  let rec insert_poly list p =
    match list with
    | [] -> [p]  (* If the list is empty, insert the monomial p *)
    | Mono(a, b) :: reste -> 
        (* Direct pattern matching of p *)
        match p with
        | Mono(a_p, b_p) -> 
            if a + a_p = 0 then 
              reste (* if equals 0, ignore the monomial *)
            else if b = b_p then (* If the powers are the same, add the coefficients *)
              Mono(a + a_p, b) :: reste  (* Update the coefficient and keep the rest of the list *)
            else
              Mono(a, b) :: insert_poly reste p  (* Otherwise, keep the current monomial and recurse *)

  (* Canonical form function to combine terms with the same power, sort by power and remove the elements with a coeff = 0 *)
  let canonique p = 
    let rec aux_func p list = 
      match p with
      | [] -> list
      | hd :: t -> aux_func t (insert_poly list hd)
    in 
    List.sort (fun (Mono(_, d1)) (Mono(_, d2)) -> compare d1 d2) (aux_func p []);;

  (* Example polynomial *)
  let poly = [Mono(3, 2); Mono(4, 1); Mono(2, 2); Mono(5, 0)] ;;
  canonique poly;;

  (* QS 1.3: Addition of two polynomials *)
  let poly2 = [Mono(5, 2); Mono(8, 1); Mono(6, 2); Mono(3, 0)] ;;

  let rec poly_add p1 p2 =
    let aux q1 q2 = 
      match p1 with
      | [] -> q2
      | hd :: reste -> poly_add reste (insert_poly q2 hd)
    in canonique (aux p1 p2);;

  (* Test the addition of two canonical polynomials *)
  poly_add (canonique poly) (canonique poly2);;

  (* QS 1.4: Multiplication of two polynomials *)
  let rec poly_prod p1 p2 =
    let rec apply_prod monome polynome = 
      match monome, polynome with
      | _,[] -> [] 
      | Mono(p1_a, p1_b), Mono(p2_a, p2_b) :: t 
        -> Mono(p1_a * p2_a, p1_b + p2_b) :: apply_prod monome t
    in 
    match p1 with
    | [] -> []
    | h::t -> poly_add (apply_prod h p2) (poly_prod t p2);;

(* Test the addition of two canonical polynomials *)
poly_add (canonique poly) (canonique poly2);;
poly_prod (canonique poly) (canonique poly2);;
(*let rec poly_prod p1 p2 = 
   match (p1, p2) with
   | (_, []) -> []  (* Empty polynomial times another polynomial is empty *)
   | ([], _) -> []  (* Same as above *)
   | (Mono(p1_a, p1_b) :: reste), (Mono(p2_a, p2_b) :: reste2) ->
       canonique (Mono(p1_a * p2_a, p1_b + p2_b) :: poly_prod reste reste2);;*)

(* QS 1.5*)
(* Expr type , rather than making a string that takes diff output like int add blabla
i made type for Add Mul and Pow to make it easier to use than interpreting a string*)
type expr = 
  | Int of int          (* Represents a number *) 
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
  | Pow [base; Int n] -> [Mono(1, n)]
  | Add children -> 
      let rec add_polys kids list = 
        match kids with
        | [] -> list
        | h :: t -> 
            let poly_hd = arb2poly h in  (* Convert the subtree into a polynomial *)
            add_polys t (canonique (poly_hd @ list))  (* Add the polynomial to the list and recurse *)
                                                      
      in
      add_polys children [];
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
  
                 
(*let rec arb2poly expr_tree =
   match expr_tree with
   | Empty -> []  (* Empty tree corresponds to an empty polynomial *)
   | Node (Int n, []) -> [Mono(n, 0)]  (* A constant becomes a monomial with exponent 0 *)
   | Node (Var x, []) -> [Mono(1, 1)]  (* A variable is treated as x^1 *)
   | Node (Add, children) -> 
       let rec add_polys kids list = 
         match kids with
         | [] -> list
         | hd :: tl -> 
             let poly_hd = arb2poly hd in  (* Convert the subtree into a polynomial *)
             add_polys tl (canonique (poly_hd @ list))  (* Add the polynomial to the list and recurse *)
       in
       add_polys children [];
   | Node (Mul, [mul ; node]) -> poly_prod (canonique(expr_tree mul)) (canonique (expr_tree node))
   | Node (Pow, [base; exp]) -> 
        (* basically because in ocaml the return types have to be similar , the int returns a Mono(n,0)
        and the n is what represents the integer , so we get that n and we make it into an expo.*)
       let exp_poly = arb2poly exp in
       match exp_poly with
       | [Mono(e, _)] -> [Mono(1, e)]  (* Return Mono(1, e) in a list of monomials *)
       | _ -> []  (* Return an empty list of monomials if the exponent isn't a simple integer *)*)


(* old version
let rec arb2poly expr_tree =
    match expr_tree with
    | Empty -> []  (* Empty tree corresponds to an empty polynomial *)
    | Node (Int n, []) -> [Mono(n, 0)]  (* A constant becomes a monomial with exponent 0 *)
    | Node (Var x, []) -> [Mono(1, 1)]  (* A variable is treated as x^1 *)
    | Node (Add, children) -> 
        let rec add_polys kids list = 
            match kids with
            | [] -> list
            | hd :: tl -> 
                let poly_hd = arb2poly hd in  (* Convert the subtree into a polynomial *)
                add_polys tl (canonique (poly_hd @ list))  (* Add the polynomial to the list and recurse *)
            in
            add_polys children [];
    | Node (Mul, [mul ; node]) -> poly_prod (canonique(expr_tree mul)) (canonique (expr_tree node));
    | Node (Pow, [base; exp]) -> 
        (* basically because in ocaml the return types have to be similar , the int returns a Mono(n,0)
        and the n is what represents the integer , so we get that n and we make it into an expo.*)
        let exp_poly = arb2poly exp in
        match exp_poly with
        | [Mono(e, _)] -> [Mono(1, e)]  (* Return Mono(1, e) in a list of monomials *)
        | _ -> []  (* Return an empty list of monomials if the exponent isn't a simple integer *)
*)

(* QS 1.8 *)
let rec remove_element n l = 
  match l with
  | [] -> []
  | h::t when n = 0 -> t
  | h::t -> h :: remove_element (n - 1) t;;

let extraction_alea list_L list_P =
  if List.length list_L = 0 then ([], list_P)
  else
    let random_int l = Random.int (List.length l) in (*defined l but never used , // will remove it*)
  (* TODO : Random.self_init() *)
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

(* Just to improve readability and removing redundance
let rec insertABR elt tree = 
  match tree with
  | Empty -> Node(Empty, elt, Empty)
  | Node (left, root, right) when elt < root -> Node(insertABR elt left, root, right)
  | Node (left, root, right) -> Node(left, root, insertABR elt right);;
  *)
let rec insertABR elt tree = 
match tree with
  | Empty -> Node(Empty, elt, Empty)
  | Node (left, root, right) -> if elt < root then Node(insertABR elt left, root, right)
                              else Node(left,root, insertABR elt right);;

let abr list = 
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
      if (root mod 2) = 1 then Mul [Int ((Random.int 401) - 200); Var "x"] else Pow [Var "x"; Int (Random.int 101)] 
  | Empty -> if Random.int 2 = 0 then Var "x" else Int (Random.int 101)
  | Node (left, root, right) -> 
      if (Random.int 4) <> 0 then Add [etiquetage left; etiquetage right] else Mul [etiquetage left; etiquetage right];; 
  
let etiq_test = etiquetage abr_test;; 

(* QS 1.12 *)

(*let rec gen_arb tree = 
   match tree with
   | Add [left; right] when left = Add [subLeft; subRight] -> Add [subLeft; subRight; right]
   | Add [left; right] when right = Add [subLeft; subRight] -> Add [left; subLeft; subRight]
   | Mul [left; right] when left = Mul [subLeft; subRight] -> Mul [subLeft; subRight; right]
   | Mul [left; right] when right = Mul [subLeft; subRight] -> Mul [left; subLeft; subRight]
   | Pow [left; right] -> if right = Int 0 then Int 1 (* right child is always the Int in the Pow node *) 
   | Add [left; right] when left = Var "x" -> Add [Pow [Var "x"; Int 1]; right]
   | Add [left; right] when right = Var "x" -> Add [left; Pow [Var "x"; Int 1]]
   | Mul [left; right] when left = Var "x" -> Mul [Pow [Var "x"; Int 1]; right]
   | Mul [left; right] when right = Var "x" -> Mul [left; Pow [Var "x"; Int 1]]*)

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

let list_ABR = generer_n_ABR 100 20;;
let transformed_ABR_list = transform_ABR list_ABR;;

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
  
let list_ABR2 = generer_n_ABR 10 20;;
let transformed_ABR_list2 = transform_ABR list_ABR2;; 

let testNaiveExo14 = add_n_tree_to_poly_naive transformed_ABR_list2;;
let testFusionExo14 = add_n_tree_to_poly_fusion transformed_ABR_list2;; 
let testDivideExo14 = add_n_tree_to_poly_divide transformed_ABR_list2;;

(* Evaluate the execution time of a function *) 
let time f x =
  let start = Sys.time() in 
  let _ = f x in
  let stop = Sys.time() in 
  stop -. start;;

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

(*let fullTestList = generate_trees 100
 let real1 = fullTest1 fullTestList
 let real2 = fullTest2 fullTestList
 let real3 = fullTest3 fullTestList*)
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
  in divide_and_conquer l;;

(* let testNaiveExo15 = prod_n_tree_to_poly_naive transformed_ABR_list2;; *)
(* let testFusionExo15 = prod_n_tree_to_poly_fusion transformed_ABR_list2;; *)
(* let testDivideExo15 = prod_n_tree_to_poly_divide transformed_ABR_list2;; *)

let rec fullTest4 l = match l with
  | [] -> [] 
  | h::t -> time add_n_tree_to_poly_naive h :: fullTest1 t;;

let rec fullTest5 l = match l with
  | [] -> [] 
  | h::t -> time add_n_tree_to_poly_fusion h :: fullTest2 t;;

let rec fullTest6 l = match l with
  | [] -> [] 
  | h::t -> time add_n_tree_to_poly_divide h :: fullTest3 t;;

(*
 let real4 = fullTest4 fullTestList
 let real5 = fullTest5 fullTestList
 let real6 = fullTest6 fullTestList*)
(* QS 2.15 *)

(* QS 2.16*)

let generate_n_abr_v2 n = 
  let rec generate count prevSize = 
    if count = n then [] 
    else if (count = 0 || count = 1) then abr (gen_permutation 1) :: generate (count+1) 1
    else abr (gen_permutation (prevSize*2)) :: generate (count+1) (prevSize*2)
  in if n < 1 then [] else generate 0 1;;

let list_ABR3 = generate_n_abr_v2 5;;
let transformed_ABR_list3 = transform_ABR list_ABR3;; 

(* Karatsuba*)
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

(*
(* Karatsuba algorithm for multiplying polynomials *)
let rec mult_karatsuba poly1 poly2 =
  (* Base case for empty polynomials (degree 0) *)
  if (degre poly1 = 0 || degre poly2 = 0) then
    [Mono(0,0)] (* Direct multiplication for degree 1 polynomials *)
  (* Base case for degree 1 polynomials (single monomial multiplication) *)
  else if (degre poly1 = 1 && degre poly2 = 1) then
    poly_prod poly1 poly2  (* Direct multiplication for degree 1 polynomials *)
  else
    let k = max (degre poly1) (degre poly2) in  (* Determine the degree *)
    let (a0, a1) = split_poly poly1 (k / 2) in
    let (b0, b1) = split_poly poly2 (k / 2) in
    let c1 = mult_karatsuba a0 b0 in  (* Recursive multiplication for lower half *) (* to do a0*b0 equation *)
    let c2 = mult_karatsuba a1 b1 in  (* Recursive multiplication for upper half *) (* to do a1*b1 equation *)
    let c3 = poly_add a1 a0 in  (* Sum a1 + a0 *)
    let c4 = poly_add b1 b0 in  (* Sum b1 + b0 *)
    let u = mult_karatsuba c3 c4 in  (* Multiply the sums *) (* to do b1 + b0 *)
    let c5 = poly_add (poly_add u (multn c2 (-1))) (multn c1 (-1)) (* to do  (a1 + a0) (b1 + b0) - a1b1 - a0b0*) in
    let c6 = multExpo c2 (k / 2) in (*this is the a1b1 * x *)
    poly_add (poly_add c5 c6 ) c1;; (* adding all results*)

*)
(* Karatsuba algorithm for multiplying polynomials *)
let rec mult_karatsuba poly1 poly2 =
  (* Base case for empty polynomials (degree 0) *)
  if(degre poly1 = -1 || degre poly2 = -1 ) then 
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


let poly2 = [
  Mono (2, 4);  (* 2x^4 *)
  Mono (-3, 3); (* -3x^3 *)
  Mono (6, 2);  (* 6x^2 *)
  Mono (8, 1);  (* 8x^1 *)
  Mono (-5, 0); (* -5 *)
];;

let poly1 = [
  Mono (3, 6);  (* 3x^6 *)
  Mono (5, 5); g (* 5x^5 *)
  Mono (-2, 4); (* -2x^4 *)
  Mono (4, 3);  (* 4x^3 *)
  Mono (1, 1);  (* 1x^1 *)
  Mono (7, 0);  (* 7 *)
];;
(* QS 2.17 & QS 2.18 : mêmes méthodes que 2.14 et 2.15 *) 

let fullTestList_v2a = transform_ABR (generate_n_abr_v2 7);;
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
let real6_v2 = time prod_n_tree_to_poly_divide fullTestList_v2a;;

(* FFT algorithm*)
open Complex

(* Function to calculate the next power of 2 greater than or equal to n *)
let nextpowof2 n =
   let x = n in 
   let x = x lor (Int.shift_right x 1) in 
   let x = x lor (Int.shift_right x 2) in
   let x = x lor (Int.shift_right x 4) in 
   let x = x lor (Int.shift_right x 8) in 
   let x = x lor (Int.shift_right x 16) in 
   x + 1

(* Fast Fourier Transform (FFT) *)
let rec fft a n w =
   if w = one || n = 1 then a else
      let ae = Array.init (n / 2) (fun i -> a.(2 * i)) in
      let ao = Array.init (n / 2) (fun i -> a.(2 * i + 1)) in
      let r1 = fft ae (n / 2) (mul w w) in
      let r2 = fft ao (n / 2) (mul w w) in
      for i = 0 to (n / 2) - 1 do
         a.(i) <- add r1.(i) ( mul ( pow w {re = float_of_int i; im = 0.0} ) r2.(i) );
         a.(i + (n / 2)) <- sub r1.(i) ( mul ( pow w {re = float_of_int i; im = 0.0} ) r2.(i) )
      done;
      a


(* Multiply two polynomials represented as lists of coefficients *)
let multiply_pol vec1 vec2 = 
  let n1 = List.length vec1 in
  let n2 = List.length vec2 in

  (* Evaluating the degree of the product polynomial *)
  let n = nextpowof2 (n1 + n2 - 1) in  (* subtract 1 because n1 + n2 gives degree + 1 *)

  let a1 = Array.make n {re = 0.0; im = 0.0} in
  let b1 = Array.make n {re = 0.0; im = 0.0} in

  (* First polynomial *)
  for i = 0 to n1 - 1 do
    Printf.printf "Element of 1st polynomial at %d: is %f\n" i (List.nth vec1 i);
    a1.(i) <- {re = List.nth vec1 i; im = 0.0};
  done;


  (* Second polynomial *)
  for i = 0 to n2 - 1 do 
    Printf.printf "Element of 2nd polynomial at %d: is %f\n" i (List.nth vec2 i);
    b1.(i) <- {re = List.nth vec2 i; im = 0.0};
  done;

  (* Evaluating omega w *)
  let theta = 2.0 *. Float.pi /. float_of_int n in
  let w = {re = cos theta; im = sin theta} in 

  (* FFT of polynomial gives Value Repn of each polynomial *)
  let a2 = fft a1 n w in
  let b2 = fft b1 n w in 

  (* Evaluating Product polynomial in Value Repn *)
  let c1 = Array.init n (fun i -> mul a2.(i) b2.(i)) in

  (* Interpolation: Value -> Coeff *)
  let win = conj w in 
  let c2 = fft c1 n win in
  let d = Array.map (fun c -> {re = c.re /. (float_of_int n); im = 0.}) c2 in

  let poly = 
    Array.to_list (Array.mapi (fun i c -> 
      if abs_float c.re >= 0.001 then Mono(int_of_float c.re, i) else Mono(0, 0)) d)
    |> List.filter (fun m -> match m with Mono(0, 0) -> false | _ -> true) in


  poly;

(* Example usage *)

let vec1 = [1.0; 2.0; 3.0]
let vec2 = [4.0; 5.0; 6.0]
multiply_pol vec1 vec2