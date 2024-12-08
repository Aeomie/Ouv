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
