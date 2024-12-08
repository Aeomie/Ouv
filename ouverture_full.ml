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


(* Additionne deux polynomes poly1 et poly2 *)
let somme_poly poly1 poly2 =
  let rec aux poly1 poly2 tmp =
    match (poly1, poly2) with
    | ([], []) -> List.rev tmp
    | ([], poly) -> List.rev_append tmp poly
    | (poly, []) -> List.rev_append tmp poly
    | (Mono(a, b) :: t1, Mono(a2, b2) :: t2) when b = b2 ->
        let a3 = a + a2 in  (* Integer addition for coefficients *)
        if a3 = 0 then
          aux t1 t2 tmp  (* Skip the term if the result is 0 *)
        else
          aux t1 t2 (Mono(a3, b2) :: tmp)
    | (Mono(a, b) :: t1, Mono(a2, b2) :: t2) when b < b2 ->
        aux t1 poly2 (Mono(a, b) :: tmp)
    | (Mono(a, b) :: t1, Mono(a2, b2) :: t2) ->
        aux poly1 t2 (Mono(a2, b2) :: tmp)
  in
  aux poly1 poly2 [];;

(* Canonical form function to combine terms with the same power, sort by power and remove the elements with a coeff = 0 *)
(*corrected version*)
let canonique p = 
  let rec aux_func p list = 
    match p with
    | [] -> list
    | Mono(a, b) :: t -> 
        (* Combine the monomial with the list and recurse *)
        aux_func t (somme_poly list [Mono(a, b)])
  in 
  (* Combine like terms and then sort the list by degree in descending order *)
  List.sort (fun (Mono(_, d1)) (Mono(_, d2)) -> compare d2 d1) 
    (aux_func p []);;

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
  | h::t -> somme_poly (apply_prod h p2) (poly_prod t p2);;


let multn poly n =
  let rec aux poly tmp =
    match poly with
    | [] -> List.rev tmp
    | Mono(a, b) :: t -> aux t (Mono(a * n, b) :: tmp)
  in aux poly [];;

let multExpo poly n = 
  let rec aux poly tmp = 
    match poly with
    | [] -> List.rev tmp
    | Mono(a,b) :: t -> aux t (Mono(a, b + n) :: tmp)
  in aux poly [];;


let degre poly =
  let rec aux max = function
    | [] -> max
    | Mono(_, b) :: next -> 
        let new_max = if b > max then b else max in
        aux new_max next
  in
  aux (0) poly;;
  

let diff_poly poly1 poly2 = 
  somme_poly (poly1) (multn poly2 (-1));;


let split_poly poly k =
  let rec aux poly left right =
      match poly with
      | [] -> (List.rev left, List.rev right)
      | Mono(a, b) :: restpoly when b < k -> aux restpoly (Mono(a, b) :: left) right 
      | Mono(a, b) :: restpoly when b >= k-> aux restpoly left (Mono(a, b-k) :: right) 
      | _ -> failwith "Unexpected case in split_poly";
  in
  aux poly [] [];; 
  


let rec mult_karatsuba poly1 poly2 =
  if(degre poly1 = 0 || degre poly2 = 0 ) then 
    poly_prod poly1 poly2 
  else
    let k =
      let max_val = max (degre poly1) (degre poly2) in
    if max_val mod 2 = 0 then max_val else max_val+1 in
    Printf.printf"k val %d \n"k; 
    let (a0, a1) = split_poly poly1 (k/2) in
    let (b0, b1) = split_poly poly2 (k/2) in
    let c1 = mult_karatsuba a0 b0 in (* a0*b0 *)
    let c2 = mult_karatsuba a1 b1 in (* a1*b1 *)
    let c3 = somme_poly a1 a0 in (* a1 + a0 *)
    let c4 = somme_poly b1 b0 in (* b1 + b0 *)
    let u = mult_karatsuba c3 c4 in (* (a1 + a0)* (b1 + b0) *)
    let c5 = diff_poly (diff_poly u c2) c1 in
    somme_poly (somme_poly (multExpo c2 (k)) (multExpo c5 (k/2))) c1 (* final sum : (a1*b1* x^k) + (result of the parantheses) + a0*b0 *)

let poly2 = [
  Mono (2, 4);  (* 2x^4 *)
  Mono (-3, 3); (* -3x^3 *)
  Mono (6, 2);  (* 6x^2 *)
  Mono (8, 1);  (* 8x^1 *)
  Mono (-5, 0); (* -5 *)
];;

let poly1 = [
  Mono (3, 6);  (* 3x^6 *)
  Mono (5, 5); (* 5x^5 *)
  Mono (-2, 4); (* -2x^4 *)
  Mono (4, 3);  (* 4x^3 *)
  Mono (1, 1);  (* 1x^1 *)
  Mono (7, 0);  (* 7 *)
];;


let poly3 = [
  Mono (4, 3);  (* 4x^3 *)
  Mono (3, 2); (* 3x^2 *)
  Mono (2, 1);  (* 2x^1 *)
  Mono (1, 0);  (* 1*x^0 *)
];;

let poly4 = [
  Mono (1, 3);  (* 3x^6 *)
  Mono (2, 2); (* 5x^5 *)
  Mono (3, 1); (* -2x^4 *)
  Mono (4, 0);  (* 4x^3 *)
];;

let poly5 = [
  Mono (2, 2);  (* 2x^2 *)
  Mono (3, 1);  (* 3x *)
  Mono (1, 0);  (* 1 *)
];;

let poly6 = [
  Mono (1, 2);  (* x^2 *)
  Mono (1, 1);  (* x *)
  Mono (4, 0);  (* 4 *)
];;
let poly7 = [
  Mono (4, 5);  (* 4x^5 *)
  Mono (3, 4);  (* 3x^4 *)
  Mono (2, 3);  (* 2x^3 *)
  Mono (1, 2);  (* 1x^2 *)
  Mono (7, 1);  (* 7x *)
  Mono (1, 0);  (* 1 *)
];;

let poly8 = [
  Mono (3, 6);  (* 3x^6 *)
  Mono (2, 5);  (* 2x^5 *)
  Mono (1, 4);  (* 1x^4 *)
  Mono (5, 3);  (* 5x^3 *)
  Mono (1, 2);  (* 1x^2 *)
  Mono (6, 0);  (* 6 *)
];;

let poly9 = [
  Mono (1, 7);  
  Mono (66, 5);  
  Mono (1, 4);  
  Mono (1, 3);
  Mono (15, 2);  
  Mono (2, 1); 
  Mono(2,0);
];;
let poly10 = [
  Mono (-20, 7);  
  Mono (1, 6);  
  Mono (4, 5);  
  Mono (21, 4);
  Mono (5, 3);  
  Mono (2, 2); 
  Mono(1,0);
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
(* Part 1 *)
type monome = Mono of int * int;;
type polynome = Poly of monome list;;

type expr = 
  | Int of int          (* Represents a number *) 
  | Var of string
  | Pow of expr list 
  | Add of expr list
  | Mul of expr list;; 

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
  Printf.printf"n : %d \n"n;
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

    (* Print the value of n *)
    Printf.printf "The value of n is: %d\n" n;

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

    Printf.printf "filled vectors";
    (* Evaluating omega w *)
    let theta = 2.0 *. Float.pi /. float_of_int n in
    let w = {re = cos theta; im = sin theta} in 
    Printf.printf "Init w";
    (* FFT of polynomial gives Value Repn of each polynomial *)
    let a2 = fft a1 n w in
    let b2 = fft b1 n w in 

    Printf.printf "Recursion passed";
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

let vec1 = [1.0; 2.0; 3.0];
let vec2 = [4.0; 5.0; 6.0];
let poly_vec3 = [Mono(1, 0); Mono(2, 1); Mono(3, 2)];
let poly_vec4 = [Mono(4, 0); Mono(5, 1); Mono(6, 2)];

let poly2 = [
  Mono (2, 4);  (* 2x^4 *)
  Mono (-3, 3); (* -3x^3 *)
  Mono (6, 2);  (* 6x^2 *)
  Mono (8, 1);  (* 8x^1 *)
  Mono (-5, 0); (* -5 *)
];;

let poly1 = [
  Mono (3, 6);  (* 3x^6 *)
  Mono (5, 5); (* 5x^5 *)
  Mono (-2, 4); (* -2x^4 *)
  Mono (4, 3);  (* 4x^3 *)
  Mono (1, 1);  (* 1x^1 *)
  Mono (7, 0);  (* 7 *)
];;

let vec1 = [7.; 1.; 0.; 4.; -2.; 5.; 3.];
let vec2 = [-5.; 8.; 6.; -3.; 2.];
multiply_pol vec1 vec2;

(*
let get_coeffs monomes =
  List.map (fun (Mono (coeff, _degree)) -> float_of_int coeff) monomes;;
*)
let get_coeffs monomes =
  let max_degree = List.fold_left (fun max_deg (Mono (_, degree)) -> max max_deg degree) 0 monomes in
  let coeffs = Array.make (max_degree + 1) 0.0 in
  List.iter (fun (Mono (coeff, degree)) -> coeffs.(degree) <- float_of_int coeff) monomes;
  Array.to_list coeffs
;;

(* QS 1.7*)
let rec arb2poly_FTT expr_tree =
  match expr_tree with 
  | Int n -> [Mono(n, 0)]
  | Var x -> [Mono(1, 1)] 
  | Pow [base; Int n] -> [Mono(1, n)]
  | Add children -> 
      let rec add_polys kids list = 
        match kids with
        | [] -> list
        | h :: t -> 
            let poly_hd = arb2poly_FTT h in  (* Convert the subtree into a polynomial *)
            add_polys t (canonique (poly_hd @ list))  (* Add the polynomial to the list and recurse *)
                                                      
      in
      add_polys children [];
  | Mul children -> 
      let rec prod_polys kids = 
        match kids with
        | [] -> [Mono(1, 0)]
        | h :: t -> 
            let poly_hd = arb2poly_FTT h in  (* Convert the subtree into a polynomial *)
            multiply_pol (get_coeffs poly_hd) (get_coeffs (prod_polys t))  (* Add the polynomial to the list and recurse *)
      in
      prod_polys children
  | _ -> [];;



  (* QS 1.7 *)
let rec arb2poly expr_tree =
  match expr_tree with 
  | Int n -> [Mono(n, 0)]  (* Integer expression converts to constant polynomial *)
  | Var x -> [Mono(1, 1)]  (* Variable x converts to polynomial x *)
  | Pow [base; Int n] -> [Mono(1, n)]  (* Power expression: x^n is represented as [Mono(1, n)] *)
  | Add children -> 
      (* Add the polynomials from the child expressions *)
      let rec add_polys kids list = 
        match kids with
        | [] -> list
        | h :: t -> 
            let poly_hd = arb2poly h in  (* Convert the subtree into a polynomial *)
            add_polys t (canonique (poly_hd @ list))  (* Combine the polynomials *)
      in
      add_polys children []
  | Mul children -> 
      (* Multiply the polynomials from the child expressions *)
      let rec prod_polys kids = 
        match kids with
        | [] -> [Mono(1, 0)]  (* Base case: empty multiplication is 1 (constant) *)
        | h :: t -> 
            let poly_hd = arb2poly h in  (* Convert the subtree into a polynomial *)
            let remaining_poly = prod_polys t in
            multiply_pol (get_coeffs poly_hd) (get_coeffs ( remaining_poly))  (* Use multiply_pol to combine the polynomials *)
      in
      prod_polys children
  | _ -> []  (* Handle unsupported cases *)