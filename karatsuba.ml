type monome = Mono of int * int;;
type polynome = Poly of monome list;;

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
  let rec aux poly1 poly2 acc =
    match (poly1, poly2) with
    | ([], []) -> acc
    | ([], p) | (p, []) -> List.rev_append acc p
    | (Mono(a, b) :: t1, Mono(a2, b2) :: t2) when b = b2 ->
        let a3 = a + a2 in
        if a3 = 0 then
          aux t1 t2 acc  (* Skip the term if the sum is 0 *)
        else
          aux t1 t2 (Mono(a3, b2) :: acc)
    | (Mono(a, b) :: t1, Mono(a2, b2) :: t2) when b < b2 ->
        aux t1 poly2 (Mono(a, b) :: acc)
    | (Mono(a, b) :: t1, Mono(a2, b2) :: t2) ->
        aux poly1 t2 (Mono(a2, b2) :: acc)
  in
  aux poly1 poly2 []  (* Directly build the list without needing to reverse it at the end *)

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
  


  let get_coeffs monomes =
    let max_degree = List.fold_left (fun max_deg (Mono (_, degree)) -> max max_deg degree) 0 monomes in
    let coeffs = Array.make (max_degree + 1) 0 in
    List.iter (fun (Mono (coeff, degree)) -> coeffs.(degree) <- coeff) monomes;
    Array.to_list coeffs
  ;;


  let multiply_lists poly1 poly2 =
    let n = List.length poly1 in
    let m = List.length poly2 in
    let result_size = n + m - 1 in  (* The resulting degree is n + m - 2, so the result has that many terms *)
  
    (* Initialize the result vector with zeros *)
    let result = Array.make result_size 0 in
  
    (* Iterate through poly1 and poly2 coefficients directly without using List.nth *)
    List.iteri (fun i a ->
      List.iteri (fun j b ->
        result.(i + j) <- result.(i + j) + a * b
      ) poly2
    ) poly1;
  
    (* Convert the result back to a list *)
    Array.to_list result
  ;;

  let multExpo poly n =
    let result_size = (List.length poly) + n in
    let result = Array.make result_size 0 in
    let rec aux i poly =
      match poly with
      | [] -> ()
      | coeff :: tail ->
          result.(i + n) <- result.(i + n) + coeff;  (* Add the coefficient to the position i + n *)
          aux (i + 1) tail
    in
    aux 0 poly;
    Array.to_list result
  ;;
  
  
  let sum_lists list1 list2 =
    let rec aux l1 l2 result =
      match l1, l2 with
      | [], [] -> List.rev result
      | x::xs, y::ys -> aux xs ys ((x + y) :: result)
      | x::xs, [] -> aux xs [] (x :: result)
      | [], y::ys -> aux [] ys (y :: result)
    in
    aux list1 list2 []
  ;;

  let diff_lists list1 list2 =
    let rec aux l1 l2 result =
      match l1, l2 with
      | [], [] -> List.rev result
      | x::xs, y::ys -> aux xs ys ((x - y) :: result)
      | x::xs, [] -> aux xs [] (x :: result)
      | [], y::ys -> aux [] ys (y :: result)
    in
    aux list1 list2 []
  ;;

(* A safe version of split_at that splits a list into two parts at the given index. *)
let rec split_at lst n =
  if n <= 0 then ([], lst)
  else match lst with
    | [] -> ([], [])
    | x :: xs -> let (left, right) = split_at xs (n - 1) in
                 (x :: left, right)

let coeffs_to_monomials coeffs =
List.fold_left (fun acc (degree, coeff) ->
  if coeff <> 0 then Mono (coeff, degree) :: acc else acc
) [] (List.mapi (fun degree coeff -> (degree, coeff)) coeffs)
|> List.rev
;;
                
(* Modify mult_karatsuba to handle recursion properly and print intermediate values *)
let rec mult_karatsuba poly1 poly2 threshold =
  if poly1 = [] || poly2 = [] then 
    []  (* Base case: if any polynomial is empty, return an empty list *)
  else 
    let deg1 = List.length poly1 in
    let deg2 = List.length poly2 in
    if deg1 < threshold || deg2 < threshold then 
      multiply_lists poly1 poly2  (* Use naive multiplication if below threshold *)
    else
      let k = 
        let max_val = max deg1 deg2 in
        if max_val mod 2 = 0 then max_val else max_val + 1 in
      (* Print the value of k *)
      (* Split poly1 and poly2 safely using split_at *)
      let (a0, a1) = split_at poly1 (k / 2) in
      let (b0, b1) = split_at poly2 (k / 2) in
      (* Print intermediate values *)
      (* Base case for small arrays, avoid breaking down further if any list is empty *)
      if List.length a0 = 0 || List.length b0 = 0 || List.length a1 = 0 || List.length b1 = 0 then
        multiply_lists poly1 poly2
      else
        let c1 = mult_karatsuba a0 b0 threshold in (* a0 * b0 *)
        let c2 = mult_karatsuba a1 b1 threshold in (* a1 * b1 *)
        let c3 = sum_lists a1 a0 in (* a1 + a0 *)
        let c4 = sum_lists b1 b0 in (* b1 + b0 *)
        let u = mult_karatsuba c3 c4 threshold in (* (a1 + a0) * (b1 + b0) *)
        let c5 = diff_lists (diff_lists u c2) c1 in
        (* Return the final result after combining the terms *)
        sum_lists (sum_lists (multExpo c2 k) (multExpo c5 (k / 2))) c1
;;


let karatsuba_threshold = 1;;
(* QS 1.7*)
let rec arb2poly_karatsuba expr_tree =
  match expr_tree with 
  | Int n -> [Mono(n, 0)]
  | Var x -> [Mono(1, 1)] 
  | Pow [base; Int n] -> [Mono(1, n)]
  | Add children -> 
      let rec add_polys kids list = 
        match kids with
        | [] -> list
        | h :: t -> 
            let poly_hd = arb2poly_karatsuba h in  (* Convert the subtree into a polynomial *)
            add_polys t (canonique (poly_hd @ list))  (* Add the polynomial to the list and recurse *)
                                                      
      in
      add_polys children [];
  | Mul children -> 
      let rec prod_polys kids = 
        match kids with
        | [] -> [Mono(1, 0)]
        | h :: t -> 
            let poly_hd = arb2poly_karatsuba h in  (* Convert the subtree into a polynomial *)
            coeffs_to_monomials(mult_karatsuba (get_coeffs(poly_hd)) (get_coeffs((prod_polys t))) karatsuba_threshold)  (* Add the polynomial to the list and recurse *)
      in
      prod_polys children
  | _ -> [];;

let tree1 =
  Add [
    Mul [Int 123; Pow [Var "x";Int 1]];
    Int 42;
    Pow [Var "x";Int 3]
  ];;
let tree2 =
  Add
    [Var "x";
      Add
        [Mul
          [Add [Int 34; Mul [Mul [Int (-5); Var "x"]; Mul [Int 80; Var "x"]]];
            Int 21];
        Mul [Var "x"; Add [Int 44; Pow [Var "x"; Int 69]]]]];;


        
(* to generate trees & test*)
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


let rec list2polyList treeList =
  match treeList with
  | [] -> []
  | h::t -> (arb2poly_karatsuba h) :: (list2polyList t);;

  

let printTime f x =
  let start = Sys.time() in 
  let _ = f x in
  let stop = Sys.time() in 
  let duration = stop -. start in
  Printf.printf "Exec time : %fs\n" duration;
  duration;;

let arb1 = transform_ABR (generer_n_ABR 100 20);;

Printf.printf("Duration for prod karatsuba\n");;

let timekaratsuba = printTime list2polyList arb1;;