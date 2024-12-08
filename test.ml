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
  if n = 1000 then [transform_ABR (generer_n_ABR n 20)]
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

(*
let treesQ14Q15 = generate_trees 100;;
let addNaiveDurationQ14 = addNaiveTest treesQ14Q15;;
let addFusionDurationQ14 = addFusionTest treesQ14Q15;;
let addDivideDurationQ14 = addDivideTest treesQ14Q15;;
*)
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

  (*
let prodNaiveDurationQ15 = prodNaiveTest treesQ14Q15;;
let prodFusionDurationQ15 = prodFusionTest treesQ14Q15;;
let prodDivideDurationQ15 = prodDivideTest treesQ14Q15;;
*)
(* Same tests *)




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
let canoniqueK p = 
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


open Complex

let nextpowof2 n =
  let x = n in 
  let x = x lor (Int.shift_right x 1) in 
  let x = x lor (Int.shift_right x 2) in
  let x = x lor (Int.shift_right x 4) in 
  let x = x lor (Int.shift_right x 8) in 
  let x = x lor (Int.shift_right x 16) in 
  x + 1;;

let rec fft a n w =
  if w = one || n = 1 then a else
      let ae = Array.init (n / 2) (fun i -> a.(2 * i)) in
      let ao = Array.init (n / 2) (fun i -> a.(2 * i + 1)) in
      let r1 = fft ae (n / 2) (mul w w) in
      let r2 = fft ao (n / 2) (mul w w) in
      for i = 0 to (n / 2) - 1 do
        a.(i) <- add r1.(i) (mul (pow w {re = float_of_int i; im = 0.0}) r2.(i));
        a.(i + (n / 2)) <- sub r1.(i) (mul (pow w {re = float_of_int i; im = 0.0}) r2.(i))
      done;
      a;;

let get_coeffs monomes =
  let max_degree = List.fold_left (fun max_deg (Mono (_, degree)) -> max max_deg degree) 0 monomes in
  let coeffs = Array.make (max_degree + 1) 0.0 in
  List.iter (fun (Mono (coeff, degree)) -> coeffs.(degree) <- float_of_int coeff) monomes;
  Array.to_list coeffs
;;
      
let mult_FFT poly1 poly2 = 
  let vec1 = get_coeffs poly1 in  (* changing poly into vectors of floats*)
  let vec2 = get_coeffs poly2 in
  (* Reading the inputs *)
  let n1 = List.length vec1 in
  let n2 = List.length vec2 in

  (* Evaluating the degree of the product polynomial *)
  let n = nextpowof2 (n1 + n2) in

  let a1 = Array.make n { re = 0.0; im = 0.0 } in
  let b1 = Array.make n { re = 0.0; im = 0.0 } in

  (* First polynomial *)
  for i = 0 to n1 - 1 do 
      a1.(i) <- { re = List.nth vec1 i; im = 0.0 };
  done;

  (* Second polynomial *)
  for i = 0 to n2 - 1 do 
      b1.(i) <- { re = List.nth vec2 i; im = 0.0 };
  done;

  (* Evaluating omega w *)
  let theta = 2.0 *. Float.pi /. float_of_int n in
  let w = { re = cos theta; im = sin theta } in 

  (* FFT of polynomial gives Value Repn of each polynomial *)
  let a2 = fft a1 n w in
  let b2 = fft b1 n w in 
  
  (* Evaluating Product polynomial in Value Repn *)
  let c1 = Array.init n (fun i -> mul a2.(i) b2.(i)) in

  (* Interpolation: Value -> Coeff *)
  let win = conj w in 
  let c2 = fft c1 n win in
  let d = Array.map (fun c -> { re = c.re /. (float_of_int n); im = 0. }) c2 in
  (* Now, we want to return the result as a list of Monomes *)
  Array.fold_left (fun pol (di, i) ->
    if((Float.round di.re) <> 0.0) then 
      Mono(int_of_float (Float.round di.re), i) :: pol
    else 
      pol
  ) [] (Array.mapi (fun i di -> (di, i)) d)
;;


let rec arb2poly_FFT expr_tree =
  match expr_tree with 
  | Int n -> [Mono(n, 0)]
  | Var x -> [Mono(1, 1)] 
  | Pow [base; Int n] -> [Mono(1, n)]
  | Add children -> 
      let rec add_polys kids list = 
        match kids with
        | [] -> list
        | h :: t -> 
            let poly_hd = arb2poly_FFT h in  (* Convert the subtree into a polynomial *)
            add_polys t (canoniqueK (poly_hd @ list))  (* Add the polynomial to the list and recurse *)
                                                      
      in
      add_polys children [];
  | Mul children -> 
      let rec prod_polys kids = 
        match kids with
        | [] -> [Mono(1, 0)]
        | h :: t -> 
            let poly_hd = arb2poly_FFT h in  (* Convert the subtree into a polynomial *)
            mult_FFT (poly_hd) (prod_polys t)  (* Add the polynomial to the list and recurse *)
      in
      prod_polys children
  | _ -> [];;


let prod_FFT l =
  let rec list2polyList treeList =
  match treeList with
  | [] -> []
  | h::t -> (arb2poly_FFT h) :: (list2polyList t)
  in
  let rec prodPolyList treeList =
    match treeList with
    | [] -> []
    | [h] -> h
    | h::t -> mult_FFT h (prodPolyList t)
    in prodPolyList (list2polyList l);;

let rec prodFFTTest l = match l with
| [] -> [] 
| h::t -> time prod_FFT h :: prodFFTTest t;;


let arb1 = transform_ABR (generer_n_ABR 100 20);;

Printf.printf("Duration for prod naive\n");;
let timeProdNaive1 = printTime prod_naive arb1;;

Printf.printf("Duration for prod fusion\n");;
let timeProdFusion1 = printTime prod_fusion arb1;;


Printf.printf("Duration for prod fusion\n");;
let timeProdDivide1 = printTime prod_fusion arb1;;

