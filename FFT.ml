open Complex
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



type expr = 
| Int of int          (* Represents a number *) 
| Var of string
| Pow of expr list 
| Add of expr list
| Mul of expr list;; 

   
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
      
let mult_FFT vec1 vec2 = 
  (* Reading the inputs *)
  let n1 = List.length vec1 in
  let n2 = List.length vec2 in

  (* Evaluating the degree of the product polynomial *)
  let n = nextpowof2 (n1 + n2) in

  let a1 = Array.make n { re = 0.0; im = 0.0 } in
  let b1 = Array.make n { re = 0.0; im = 0.0 } in

  (* First polynomial *)
  print_endline "Coefficient vector of 1st polynomial :";
  for i = 0 to n1 - 1 do 
      a1.(i) <- { re = List.nth vec1 i; im = 0.0 };
  done;

  (* Second polynomial *)
  print_endline "Coefficient vector of 2nd polynomial :";
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


(* QS 1.7*)
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
            add_polys t (canonique (poly_hd @ list))  (* Add the polynomial to the list and recurse *)
                                                      
      in
      add_polys children [];
  | Mul children -> 
      let rec prod_polys kids = 
        match kids with
        | [] -> [Mono(1, 0)]
        | h :: t -> 
            let poly_hd = arb2poly_FFT h in  (* Convert the subtree into a polynomial *)
            mult_FFT (get_coeffs(poly_hd)) (get_coeffs(prod_polys t))  (* Add the polynomial to the list and recurse *)
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
  
  