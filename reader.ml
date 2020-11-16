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

let nt_whitespaces = star (char ' ');;

let digit = range '0' '9';;

let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let make_spaced nt = make_paired nt_whitespaces (disj (nt_whitespaces) (plus (char '\n'))) nt;;

let tok_lparen = make_spaced ( char '(');;

let tok_rparen = make_spaced ( char ')');;

let tok_addop = make_spaced ( char '+');;

let tok_mulop = make_spaced ( char '*');;

let tok_semicolon = char ';';;

let nt_boolt = make_spaced ( word_ci "#t" );;

let nt_boolf = make_spaced ( word_ci "#f" );;

let nt_bool = disj nt_boolf nt_boolt;;

let nt_rightquotation = 
  make_paired (nt_epsilon) (nt_whitespaces) (char '"');;

let nt_leftquotation =
  make_paired (nt_whitespaces) (nt_epsilon) (char '"');;

let nt_metachar
  = caten (char ('\\')) (const (fun ch -> ch='f'||ch='n'||ch='\\'||ch='t'||ch='r'||ch='"'));;

let nt_fixedmetachar
  = function
    | ('\\','f') -> '\012'
    | ('\\','n') -> '\n'
    | ('\\','t') -> '\t'
    | ('\\','r') -> '\r'
    | ('\\','\\') -> '\\'
    | ('\\', '\"') -> '\"' 
    | (s, r) -> r;; (* RISKY BUT I HAD TO UNTIL I GET A REPLY*)

let rec gcd a b =
  if b = 0 then a else gcd b (a mod b);;

let do_gcd a b = 
  let x = gcd a b in
    (a/x, b/x);;

let nt_stringcontent
  = star ( disj (pack nt_metachar nt_fixedmetachar) (const (fun ch -> ch != '\"' && ch!='\\')));;

let nt_string
  = pack (caten (nt_leftquotation) (caten (nt_stringcontent) (nt_rightquotation)))
    (fun (e,(s, r)) -> s);;

let nt_natural = plus (digit);;

let nt_sign = const (fun ch -> ch='+'||ch='-');;

let nt_integer = pack (caten (maybe nt_sign) nt_natural) 
    (fun (e, s)-> match e with 
       | None -> s
       | Some(r)-> r::s);;    

let nt_float  = 
  pack (make_spaced(caten (caten (nt_integer) (char '.') ) (nt_natural)))
    (fun ((s, e), r) -> s@[e]@r);;

let nt_fracture =
  pack (make_spaced(caten (caten (nt_integer) (char '/') ) (nt_natural)))
    (fun ((s, e), r) -> s@[e]@r);;

let disj_l l nt=
  List.fold_right
    (fun x acc -> disj (nt x) (acc)) 
    l 
    nt_none;;

let nt_namedchar =
  disj_l ["#\\newline"; "#\\nul"; "#\\page"; "#\\return"; "#\\space"; "#\\tab"] word;;

let nt_visibilesimplechar =
  pack (caten (caten (word "#\\") (const (fun ch -> ch>' '))) nt_whitespaces)
    (fun ((_,c),r) -> 
       ('#'::('\\'::[c])));;

let nt_dot = (char '.');;

let nt_specialchar = disj_l ['!';'$';'^';'*';'-';'_';'+';'=';'<';'>';'?';'/';':'] char;;

let nt_symbolcharnodot = disj (nt_specialchar) (disj (digit) (range_ci 'a' 'z'));;

let nt_symbolchar = disj (nt_symbolcharnodot) (nt_dot);;

let nt_symbol = disj
(**First parser*)(pack (caten (nt_symbolchar) (plus nt_symbolchar)) (fun (s,e)->s::e))
(**Second parser*)(pack (nt_symbolcharnodot)((fun s->[s])))

let nt_disj_nt_list l= 
  List.fold_right
    (fun x acc -> disj (x) (acc))
    l
    nt_none;;

let nt_number =  nt_disj_nt_list [nt_float; nt_fracture; nt_integer];;

let nt_numberE = pack (caten (caten (nt_number) (char_ci 'e')) (nt_integer)) (fun ((e,s),r)->e@(s::r));; 

let nt_char = nt_disj_nt_list [nt_namedchar;nt_visibilesimplechar];;

let rec nt_expr s =
  let nt_nestedexp = pack (caten (caten tok_lparen nt_expr) tok_rparen)
      (fun ((l, e), r) -> e) in
  (disj nt_number nt_nestedexp) s

and nt_stringR s = 
  let st = (pack (caten (caten nt_leftquotation nt_stringcontent) nt_rightquotation)
              (fun ((l, e), r) -> String(list_to_string e))) in st s

and nt_numberR s = let nt_l = [
    pack (nt_numberE) (fun s-> Number(Float(float_of_string(list_to_string s))));
    pack (nt_float) (fun s-> Number(Float(float_of_string (list_to_string s))));
    pack (caten (caten (nt_integer) (char '/')) (nt_natural)) (fun ((s,e),r)->
        let (num, denom) = do_gcd (int_of_string (list_to_string s)) (int_of_string (list_to_string r)) in
            Number(Fraction(num,denom)));
    pack (nt_integer) (fun s-> Number(Fraction(int_of_string (list_to_string s),1)))] in
  nt_disj_nt_list nt_l s

and nt_boolR s = let nt_l = [
    pack (nt_boolf)(fun s -> Bool(false));
    pack (nt_boolt)(fun s -> Bool(true))]
  in nt_disj_nt_list nt_l s

and nt_charR s = let nt_l = [
    pack (word_ci "\\space") (fun s -> Char(' '));
    pack (word_ci "\\newline") (fun s -> Char('\n'));
    pack (word_ci "\\page") (fun s -> Char('\012'));
    pack (word_ci "\\nul") (fun s -> Char(char_of_int 0));
    pack (word_ci "\\formfeed") (fun s -> Char(char_of_int 12));
    pack (word_ci "\\return") (fun s -> Char(char_of_int 13));
    pack (const (fun ch-> ch>' ')) (fun s -> Char(s))] in
  pack (caten (word "#\\") (nt_disj_nt_list nt_l)) (fun (e,s)-> s) s

and nt_symbolR s = let nt_l = [
    pack (nt_symbol) (fun s -> Symbol(list_to_string s))] in
  nt_disj_nt_list nt_l s 

and nt_list s = let packed = (
    pack (caten (caten tok_lparen (star (nt_sexpr))) tok_rparen)
      (fun ((l, e), r) -> let folder =
                            (List.fold_right(
                                (fun x acc -> Pair(x,acc)))) in
        folder e Nil)) in 
  packed s

and nt_sexpr s =  let nt_l = [
  nt_numberR; nt_charR; nt_symbolR; nt_stringR; nt_boolR;nt_list;nt_dottedlist;nt_quote;nt_sexprcomment;nt_comment;nt_newline] in
  (make_spaced( nt_disj_nt_list nt_l)) s


and nt_dottedlist s = let car = pack (caten (caten (caten (caten(tok_lparen)(plus(nt_sexpr)))(nt_dot))(nt_sexpr))(tok_rparen))
                          (fun ((((lp,sep),dot),se),rp) -> let folder = (List.fold_right(
                               (fun x acc -> Pair(x,acc)))) in
                             folder sep se) in
  car s

and nt_quote s = pack (caten (nt_disj_nt_list[word ("\039");
                                              word ("`");
                                              word ",@";
                                              word ",";])(nt_sexpr))
                            (fun (s,e)->
                            match s with
                            | ['\039'] ->Pair(Symbol("quote"), Pair(e,Nil))
                            | ['`'] ->Pair(Symbol("quasiquote"), Pair(e,Nil))  
                            | [','; '@'] ->Pair(Symbol("unquote-splicing"), Pair(e,Nil))
                            | [','] ->Pair(Symbol("unquote"), Pair(e,Nil))
                            | _ -> raise X_no_match) s

and nt_sexprcomment s = pack (caten (caten (word "#;") (nt_sexpr)) (maybe (nt_sexpr)))
  (fun ((s,e),r)-> match r with | None -> Nil | Some r -> r ) s
  
and nt_comment s = pack (caten (caten (char ';') (star (const (fun ch -> ch!='\n')))) 
  (maybe nt_sexpr))
  (fun ((s,e),r)-> match r with | None -> Nil | Some r -> r) s

and nt_newline s = pack (caten (plus (char '\n')) (maybe nt_sexpr)) ((fun (s,e)->match e with | None -> Nil | Some r -> r)) s

and nt_exprR s = make_spaced (star nt_sexpr) s ;;

let read_sexprs string =  let (ret,tail) = nt_exprR (string_to_list (string))
    in match tail with | [] -> ret | _ -> raise X_no_match ;;

end;;