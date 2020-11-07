
#use "pc.ml";;
open PC

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
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2);;
  
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

let nt_whitespaces = star (char ' ');;

let digit = range '0' '9';;

let make_paired nt_left nt_right nt =
let nt = caten nt_left nt in
let nt = pack nt (function (_, e) -> e) in
let nt = caten nt nt_right in
let nt = pack nt (function (e, _) -> e) in
  nt;;

let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;

let tok_lparen = make_spaced ( char '(');;

let tok_rparen = make_spaced ( char ')');;

let tok_addop = make_spaced ( char '+');;

let tok_mulop = make_spaced ( char '*');;

let nt_bool = make_spaced ( disj 
    (caten (char '#') (char 't'))  (caten (char '#') (char 'f')) );; 
end;;



















(* struct Reader *)
(**
This is a list of things that I should add a parser to.
First lets define out "Tokens" so far, it will be basically any string not containing backspace, or other
char with value less than backspace.
now lets take a look at our non-terminals: (last updated NOV.4)
1-
⟨Sexpr⟩ ::= ⟨Boolean⟩ | ⟨Char⟩ | ⟨Number⟩ | ⟨String⟩
| ⟨Symbol⟩ | ⟨List⟩ | ⟨DottedList⟩ | ⟨Quoted⟩
| ⟨QuasiQuoted⟩ | ⟨Unquoted⟩
| ⟨UnquoteAndSpliced⟩
Here
@TODO on 4.NOVEMBER  (STATUS: DONE) : nt_bool(v),
@TODO on 5.NOVEMBER  (STATUS: DONE) : make nt Strings(v), make nt Char(v).
@TODO on 6.NOVEMBER  (STATUS: PENDING): finish nt_symbol, it will be tricky since it takes one char or more.


////******Updates******////
4.NOV: for tomorrow: WATCH out from case sensitive/insensitive when working with char/string nt.
WORK on TestingShit and not here, add the functions here when you are done testing!!!
5.NOV: Encountered a problem in strings, what should I do when I encounter "\u", turn it into a string?
I HAVE MANAGED TO MAKE A PARSER THAT PARSES STRING/NUMBER/CHAR, what is left now the symbol

**)