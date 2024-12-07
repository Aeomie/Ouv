open Complex

type monome = Mono of int * int;;
type polynome = Poly of monome list;;

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

let vec1 = [1.0; 2.0; 3.0];
let vec2 = [4.0; 5.0; 6.0];
multiply_pol vec1 vec2;