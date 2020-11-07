(* pc.ml
 * A parsing-combinators package for ocaml
 *
 * Prorammer: Mayer Goldberg, 2018
 *)

(* general list-processing procedures *)

let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  

let lowercase_ascii  =
  let delta = int_of_char 'A' - int_of_char 'a' in
  fun ch ->
  if ('A' <= ch && ch <= 'Z')
  then char_of_int ((int_of_char ch) - delta)
  else ch;;

let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

let list_to_string s =
  String.concat "" (List.map (fun ch -> String.make 1 ch) s);;

module PC = struct

(* the parsing combinators defined here *)
  
exception X_not_yet_implemented;;

exception X_no_match;;

let const pred =
  function 
  | [] -> raise X_no_match
  | e :: s ->
     if (pred e) then (e, s)
     else raise X_no_match;;

let caten nt1 nt2 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  ((e1, e2), s);;

let pack nt f s =
  let (e, s) = (nt s) in
  ((f e), s);;

let nt_epsilon s = ([], s);;

let caten_list nts =
  List.fold_right
    (fun nt1 nt2 ->
     pack (caten nt1 nt2)
	  (fun (e, es) -> (e :: es)))
    nts
    nt_epsilon;;

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_no_match -> (nt2 s);;

let nt_none _ = raise X_no_match;;
  
let disj_list nts = List.fold_right disj nts nt_none;;


let delayed thunk s =
  thunk() s;;

let nt_end_of_input = function
  | []  -> ([], [])
  | _ -> raise X_no_match;;

let rec star nt s =
  try let (e, s) = (nt s) in
      let (es, s) = (star nt s) in
      (e :: es, s)
  with X_no_match -> ([], s);;

let plus nt =
  pack (caten nt (star nt))
       (fun (e, es) -> (e :: es));;

let guard nt pred s =
  let ((e, _) as result) = (nt s) in
  if (pred e) then result
  else raise X_no_match;;
  
let diff nt1 nt2 s =
  match (let result = nt1 s in
	 try let _ = nt2 s in
	     None
	 with X_no_match -> Some(result)) with
  | None -> raise X_no_match
  | Some(result) -> result;;

let not_followed_by nt1 nt2 s =
  match (let ((_, s) as result) = (nt1 s) in
	 try let _ = (nt2 s) in
	     None
	 with X_no_match -> (Some(result))) with
  | None -> raise X_no_match
  | Some(result) -> result;;
	  
let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

(* useful general parsers for working with text *)

let make_char equal ch1 = const (fun ch2 -> equal ch1 ch2);;

let char = make_char (fun ch1 ch2 -> ch1 = ch2);;

let char_ci =
  make_char (fun ch1 ch2 ->
	     (lowercase_ascii ch1) =
	       (lowercase_ascii ch2));;

let make_word char str = 
  List.fold_right
    (fun nt1 nt2 -> pack (caten nt1 nt2) (fun (a, b) -> a :: b))
    (List.map char (string_to_list str))
    nt_epsilon;;

let word = make_word char;;

let word_ci = make_word char_ci;;

let make_one_of char str =
  List.fold_right
    disj
    (List.map char (string_to_list str))
    nt_none;;

let one_of = make_one_of char;;

let one_of_ci = make_one_of char_ci;;

let nt_whitespace = const (fun ch -> ch <= ' ');;

let make_range leq ch1 ch2 (s : char list) =
  const (fun ch -> (leq ch1 ch) && (leq ch ch2)) s;;

let range = make_range (fun ch1 ch2 -> ch1 <= ch2);;

let range_ci =
  make_range (fun ch1 ch2 ->
	      (lowercase_ascii ch1) <=
		(lowercase_ascii ch2));;

let nt_any (s : char list) = const (fun ch -> true) s;;

let trace_pc desc nt s =
  try let ((e, s') as args) = (nt s)
      in
      (Printf.printf ";;; %s matched the head of \"%s\", and the remaining string is \"%s\"\n"
		     desc
		     (list_to_string s)
		     (list_to_string s') ;
       args)
  with X_no_match ->
    (Printf.printf ";;; %s failed on \"%s\"\n"
		   desc
		   (list_to_string s) ;
     raise X_no_match);;

(* testing the parsers *)

let test_string nt str =
  let (e, s) = (nt (string_to_list str)) in
  (e, (Printf.sprintf "->[%s]" (list_to_string s)));;

end;; (* end of struct PC *)

(* end-of-input *)



(* We assert that the work we submitted is 100% our own. We have not received any part from any other student in the class, nor have we give parts of it for use to others. Nor have we used code from other sources: Courses taught previously at this university, courses taught at other universities, various bits of code found on the Internet, etc. *)
(* We realize that should our code be found to contain code from other sources, that a formal case shall be opened against us with va’adat mishma’at, in pursuit of disciplinary action. *)
(* #use "pc.ml";; *)
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  |_ -> raise X_no_match;;

  
module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexprs string = raise X_not_yet_implemented;;
  
end;; (* struct Reader *)
let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
    nt;;
   
let nt_whitespaces = star (char ' ');;

let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;

let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

let digit = range '0' '9';;

let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

let get_option some_val =
  match some_val with
    | Some a -> a
    | None -> None;;

(* -------------------------------------------------------------------------------------------------------- *)

let string_metachar
  = caten (char ('\\')) (const (fun ch -> ch='f'||ch='n'||ch='\\'||ch='t'||ch='r'||ch='"'));;

let replace_metachar s = 
  match s with
    | ('\\','f') -> '\012'
    | ('\\','n') -> '\n'
    | ('\\','t') -> '\t'
    | ('\\','r') -> '\r'
    | ('\\','\\') -> '\\'
    | ('\\', '\"') -> '\"'
    | (s, r) -> raise X_no_match;;


let stringLiteralChar =  (const (fun ch -> ch!='\"' && ch!= '\\'));;

let strignChar
  = disj (pack string_metachar replace_metachar) stringLiteralChar;;

let rec gcd a b =
  if b = 0 then a else gcd b (a mod b);;

let do_gcd a b = 
  let x = gcd a b in
    (a/x, b/x);;


let tenEx num ex = 
  let rec pow a = function
    | 0 -> 1.
    | 1 -> a
    | n -> 
      let b = pow a (n / 2) in
      b *. b *. (if n mod 2 = 0 then 1. else a) in
  let times = pow 10. ex in
  num *. times;;

(* -------------------------------------------------------------------------------------------------------- *)



(* let nt_numberE = pack (caten (caten (nt_number) (char_ci 'e')) (nt_integer)) (fun ((e,s),r)->e@(s::r));;  *)

let nt_boolt = make_spaced (word_ci "#t");;

let nt_boolf = make_spaced (word_ci "#f");;

let tok_lparen = make_spaced ( char '(');;

let tok_rparen = make_spaced ( char ')');;

let tok_addop = make_spaced ( char '+');;

let tok_mulop = make_spaced ( char '*');;

let tok_semicolon = char ';';;

let nt_rightquotation = 
  make_paired (nt_epsilon) (nt_whitespaces) (char '"');;

let nt_leftquotation =
  make_paired (nt_whitespaces) (nt_epsilon) (char '"');;

let disj_l l nt =
  List.fold_right
    (fun x acc -> disj (nt x) (acc)) 
    l 
    nt_none;;

let nt_disj_nt_list l= 
  List.fold_right
    (fun x acc -> disj (x) (acc))
    l
    nt_none;;


(* ------------------------------------------------ Compilers ----------------------------------------------- *)




  (* ----------------  symbol -----------------*)
let nt_specialchar = disj_l ['!';'$';'^';'*';'-';'_';'+';'=';'<';'>';'?';'/';':'] char;;
let symNums = range '0' '9';;
let symLetters = range_ci 'a' 'z';;
let symbolCharNoDot = disj (disj symNums symLetters) nt_specialchar;;
let dot = (char '.');;
let symChar = disj symbolCharNoDot dot;;


  (* ----------------  number -----------------*)
let natural =
  let digits = make_spaced (plus digit) in
  pack digits (fun (ds) -> ds);;

let sign = maybe (fun s -> 
  match s with
  | []-> raise X_no_match
  | car::cdr ->  if (car = '+') || (car = '-') 
      then (car, cdr) 
        else raise X_no_match);;

let integer = pack (caten sign natural) (fun s ->
  match s with
  |(Some a, num) -> a::num
  |((None, num)) -> num
  );;

let fraction = caten (caten integer (char '/')) natural;;

let floats = caten (caten integer dot) natural;;

let exponent_float (((domi, symb), nomi), expo) = match symb with
      |'.' -> (match expo with |'e'::rest -> Number(Float(float_of_string (list_to_string (domi@symb::nomi@expo))))
                               |_ -> raise X_no_match)
      |'_' -> (match expo with  | 'e'::rest -> Number(Float(float_of_string (list_to_string (domi@expo))))
                                |_ -> raise X_no_match)
      |_-> raise X_no_match
                                

let number s = 
    let (((domi, symb), nomi), rest) = 
      try (fraction s)
      with PC.X_no_match -> (
        try (floats s)
        with PC.X_no_match -> pack integer (fun x -> ((x, '_'), ['1'])) s
      ) 
      in
      let (scientific, rest) = maybe (char 'e') rest in
      let (exponent, rest) = match scientific with
      |Some(e) -> integer rest
      |None -> (['_'], rest) in
      let (sexp) = 
      disj exponent_float (fun (((domi, symb), nomi), exponent) -> match symb with
      | '.' -> Number(Float(float_of_string (list_to_string (domi@symb::nomi))))
      | '_' -> (Number(Fraction((int_of_string (list_to_string domi)), (int_of_string (list_to_string nomi)))))
      | '/' -> let(domi, nomi) = do_gcd (int_of_string (list_to_string domi)) (int_of_string (list_to_string nomi)) in (Number(Fraction(domi, nomi)))
      | _-> raise X_no_match) (((domi, symb), nomi), exponent) in
      (sexp, rest)


let charPrefix s = word "#\\" s;;

let visiblesimplechar s = const (fun ch -> ch >' ') s;;

let nt_namedChar s = 
  let (e,s) = disj_l ["newline"; "nul"; "page"; "return"; "space"; "tab"] word s in
  let e = (list_to_string e) in
  match e with
    |"newline" -> ('\n', s)
    |"nul" -> ('\000', s)
    |"page" -> ('\012',s)
    |"return" -> ('\013',s)
    |"space" -> (' ',s)
    |"tab" ->('\t', s)
    |e -> raise X_no_match;;


let rec nt_expr s =
  let nt_nestedexp = pack (caten (caten tok_lparen nt_expr) tok_rparen)
      (fun ((l, e), r) -> e) in
  (disj nt_number nt_nestedexp) s

and nt_string s = 
  let st = (pack (caten (caten nt_leftquotation (star  strignChar)) nt_rightquotation)
                (fun ((l, e), r) -> String(list_to_string e))) in st s
        

and nt_bool = disj (pack nt_boolt (fun _-> Bool(true))) 
  (pack nt_boolf (fun _-> Bool(false)))


and nt_char = pack (caten (caten charPrefix (disj visiblesimplechar nt_namedChar)) nt_whitespaces) 
      (fun ((pre, vis), spaces) -> Char(vis))

and nt_number =  number

and nt_symbol =  disj (fun s -> let (sym,rest) = symbolCharNoDot s in
        (Symbol(list_to_string [sym]), rest)) (fun x ->
  let ((sym,slst), rest) = caten symChar (plus symChar) x in
  (Symbol(list_to_string (sym::slst)), rest))

and nt_list s = let p = pack 
    (caten (caten tok_lparen (star (nt_sexpr))) tok_rparen) 
      (fun ((l,exps), r) -> (List.fold_right(
                (fun x acc  -> Pair(x ,acc)))) exps Nil)
                 in p s

and nt_dotted_list s = let dotted = pack 
      (caten (caten tok_lparen (plus nt_sexpr)) (caten dot (caten nt_sexpr tok_rparen)))
              (fun ((l, exps),(d,(exp, r))) -> (List.fold_right((fun x acc -> Pair(x, acc)))) exps exp 
              )
              in dotted s
and nt_all_quotes s = let (quete,sexp) = match s with
      | '\''::rest -> ("quote",rest)
      | '`'::rest -> ("quasiquote",rest)
      | ','::rest -> (match rest with 
                        | '@'::rest_2 -> ("unquote-splicing",rest_2)
                        |_ -> ("unquote",rest)
                      )
      |_ -> raise X_no_match 
      in let (s,r) = nt_sexpr sexp in 
      (Pair(Symbol(quete), Pair(s, Nil)), r)


and nt_sexpr s =  let nt_l = [
  nt_number; nt_char;nt_string; nt_bool;nt_symbol;nt_list;nt_dotted_list] in
  (make_spaced(nt_disj_nt_list nt_l)) s;;