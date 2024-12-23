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

(* Same tests *)
(* Additionne deux polynomes poly1 et poly2 *)

  (**************************************************************************************************************************************)
  (**************************************************************************************************************************************)
  (******************************************************* KARATSUBA ********************************************************************)
  (**************************************************************************************************************************************)
  (**************************************************************************************************************************************)
  let canonique_plus p = 
    let rec aux_func p list = 
      match p with
      | [] -> list
      | Mono(a, b) :: t -> 
          (* Combine the monomial with the list and recurse *)
          aux_func t (poly_add list [Mono(a, b)])
    in 
    (* Combine like terms and then sort the list by degree in descending order *)
    List.sort (fun (Mono(_, d1)) (Mono(_, d2)) -> compare d2 d1) 
      (aux_func p []);;

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
    let rec aux poly1 poly2 tmp =
      match (poly1, poly2) with
      | ([], []) -> List.rev tmp
      | ([], poly) -> List.rev_append tmp poly
      | (poly, []) -> List.rev_append tmp poly
      | (Mono(a, b) :: t1, Mono(a2, b2) :: t2) when b = b2 ->
          let a3 = a - a2 in  (* Integer addition for coefficients *)
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
    let deg1 = degre poly1 in
    let deg2 = degre poly2 in
    if(deg1 = 0 || deg2 = 0 ) then 
      poly_prod poly1 poly2 
    else
      let k =
        let max_val = max (deg1) (deg2) in
      if max_val mod 2 = 0 then max_val else max_val+1 in
      let (a0, a1) = split_poly poly1 (k/2) in
      let (b0, b1) = split_poly poly2 (k/2) in
      let c1 = mult_karatsuba a0 b0 in (* a0*b0 *)
      let c2 = mult_karatsuba a1 b1 in (* a1*b1 *)
      let c3 = poly_add a1 a0 in (* a1 + a0 *)
      let c4 = poly_add b1 b0 in (* b1 + b0 *)
      let u = mult_karatsuba c3 c4 in (* (a1 + a0)* (b1 + b0) *)
      let c5 = diff_poly (diff_poly u c2) c1 in
      poly_add (poly_add (multExpo c2 (k)) (multExpo c5 (k/2))) c1 (* final sum : (a1*b1* x^k) + (result of the parantheses) + a0*b0 *)

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
              add_polys t (canonique_plus (poly_hd @ list))  (* Add the polynomial to the list and recurse *)
                                                        
        in
        add_polys children [];
    | Mul children -> 
        let rec prod_polys kids = 
          match kids with
          | [] -> [Mono(1, 0)]
          | h :: t -> 
              let poly_hd = arb2poly_karatsuba h in  (* Convert the subtree into a polynomial *)
              mult_karatsuba poly_hd (prod_polys t)  (* Add the polynomial to the list and recurse *)
        in
        prod_polys children
    | _ -> [];;

  (**************************************************************************************************************************************)
  (**************************************************************************************************************************************)
  (******************************************************* KARATSUBA V2 *****************************************************************)
  (**************************************************************************************************************************************)
  (**************************************************************************************************************************************)
  let get_coeffs_karatsuba monomes =
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
let rec mult_karatsuba_2 poly1 poly2 threshold =
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
        let c1 = mult_karatsuba_2 a0 b0 threshold in (* a0 * b0 *)
        let c2 = mult_karatsuba_2 a1 b1 threshold in (* a1 * b1 *)
        let c3 = sum_lists a1 a0 in (* a1 + a0 *)
        let c4 = sum_lists b1 b0 in (* b1 + b0 *)
        let u = mult_karatsuba_2 c3 c4 threshold in (* (a1 + a0) * (b1 + b0) *)
        let c5 = diff_lists (diff_lists u c2) c1 in
        (* Return the final result after combining the terms *)
        sum_lists (sum_lists (multExpo c2 k) (multExpo c5 (k / 2))) c1
;;


let karatsuba_threshold = 1;;

let rec arb2poly_karatsuba_2 expr_tree =
  match expr_tree with 
  | Int n -> [Mono(n, 0)]
  | Var x -> [Mono(1, 1)] 
  | Pow [base; Int n] -> [Mono(1, n)]
  | Add children -> 
      let rec add_polys kids list = 
        match kids with
        | [] -> list
        | h :: t -> 
            let poly_hd = arb2poly_karatsuba_2 h in  (* Convert the subtree into a polynomial *)
            add_polys t (canonique (poly_hd @ list))  (* Add the polynomial to the list and recurse *)
                                                      
      in
      add_polys children [];
  | Mul children -> 
      let rec prod_polys kids = 
        match kids with
        | [] -> [Mono(1, 0)]
        | h :: t -> 
            let poly_hd = arb2poly_karatsuba_2 h in  (* Convert the subtree into a polynomial *)
            coeffs_to_monomials(mult_karatsuba_2 (get_coeffs_karatsuba(poly_hd)) (get_coeffs_karatsuba((prod_polys t))) karatsuba_threshold)  (* Add the polynomial to the list and recurse *)
      in
      prod_polys children
  | _ -> [];;

  (**************************************************************************************************************************************)
  (**************************************************************************************************************************************)
  (******************************************************* FTT **************************************************************************)
  (**************************************************************************************************************************************)
  (**************************************************************************************************************************************)
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
              add_polys t (canonique_plus (poly_hd @ list))  (* Add the polynomial to the list and recurse *)
                                                        
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

  let prod_karatsuba l =
    let rec list2polyList treeList =
    match treeList with
    | [] -> []
    | h::t -> (arb2poly_karatsuba h) :: (list2polyList t)
    in
    let rec prodPolyList treeList =
    match treeList with
    | [] -> []
    | [h] -> h
    | h::t -> mult_karatsuba h (prodPolyList t)
    in prodPolyList (list2polyList l);;

  let arb1 = transform_ABR (generer_n_ABR 100 20);;

  let rec list2polyList_FFT treeList =
    match treeList with
    | [] -> []
    | h::t -> 
        (* Print the current tree number *)
        (* Process the current tree element and recurse with incremented count *)
        (arb2poly_FFT h) :: (list2polyList_FFT t);;

  let rec list2polyList_karatsuba2 treeList =
    match treeList with
    | [] -> []
    | h::t -> (arb2poly_karatsuba_2 h) :: (list2polyList_karatsuba2 t);;

  let rec list2polyList_karatsuba treeList =
    match treeList with
    | [] -> []
    | h::t -> (arb2poly_karatsuba h) :: (list2polyList_karatsuba t);;
  
  Printf.printf("Karatsuba tree gen : \n");;
  let timekaratsuba = printTime list2polyList_karatsuba arb1;;
  Printf.printf("Duration for prod karatsuba\n");;
  let timekaratsuba = printTime prod_karatsuba arb1;;
  Printf.printf("FFT tree gen : \n");;
  let timeFFT = printTime list2polyList_FFT arb1 ;;
  Printf.printf("Karatsuba v2 tree gen : \n");;
  let timekaratsuba = printTime list2polyList_karatsuba2 arb1;;

