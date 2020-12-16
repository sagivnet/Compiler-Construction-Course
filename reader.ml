
(* semantic-analyser.ml
 * A compiler from Scheme to x86/64
 *
 * Programmers: Sagiv Nethanel & Eran Levav, 2018
 *)
 (***************************************************************************************************)
 (***************************************************************************************************)
 #use "pc.ml";;
 open PC;;
 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
 exception X_nt_hex_float_helper_error;;
 exception X_nt_hex_int_helper;;
 exception X_nt_reg_int_helper;;

 type number =
   | Int of int
   | Float of float;;

 type sexpr =
   | Bool of bool
   | Nil
   | Number of number
   | Char of char
   | String of string
   | Symbol of string
   | Pair of sexpr * sexpr
   | Vector of sexpr list;;
 
   let rec sexpr_eq s1 s2 =
     match s1, s2 with
     | Bool(b1), Bool(b2) -> b1 = b2
     | Nil, Nil -> true
     | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
     | Number(Int n1), Number(Int n2) -> n1 = n2
     | Char(c1), Char(c2) -> c1 = c2
     | String(s1), String(s2) -> s1 = s2
     | Symbol(s1), Symbol(s2) -> s1 = s2
     | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
     | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
     | _ -> false;;

(***************************************************************************************************)
(******************************************** General Parsers **************************************)
(***************************************************************************************************)

 let nt_digit  = range '0' '9';;
 let nt_lparen = (char '(');;
 let nt_rparen = (char ')');;
 let nt_sq_lparen = (char '[');;
 let nt_sq_rparen = (char ']');;
 let nt_open = disj nt_lparen nt_sq_lparen ;;
 let nt_close = disj nt_rparen nt_sq_rparen ;;
 let nt_close_all = word "..." ;;


(***************************************************************************************************)
(******************************************** Char Parser ******************************************)
(***************************************************************************************************)
 (*⟨Char⟩::=⟨CharPrefix⟩ ( ⟨VisibleSimpleChar⟩*)
 (*| ⟨NamedChar⟩ | ⟨HexChar⟩ )*)

 let nt_char_prefix = (word "#\\") ;;
 let nt_letter = range_ci 'a' 'z';;
 
 let nt_hex_prefix = (word_ci "#\\x");;
 let nt_hex_digit = disj (range '0' '9') (range_ci 'a' 'f');;
 
 let nt_simple_char = const (fun ch -> ch > ' ') ;;
 let nt_named_char = disj_list [(pack (word_ci "newline") (fun ch -> Char.chr 10)) ;
                                (pack (word_ci "nul") (fun ch -> Char.chr 0))      ;
                                (pack (word_ci "page") (fun ch -> Char.chr 12))    ;
                                (pack (word_ci "return") (fun ch -> Char.chr 13))  ;
                                (pack (word_ci "space") (fun ch -> Char.chr 32))   ;
                                (pack (word_ci "tab") (fun ch -> Char.chr 9))]    ;;
 let nt_char s = 
   let char_normal = caten nt_char_prefix (disj nt_named_char nt_simple_char) in
   let char_normal = pack char_normal (fun (hd,tl) -> Char tl ) in
 
     let char_hex = caten nt_hex_prefix (plus nt_hex_digit) in
     let char_hex = pack char_hex (fun (hd,tl) -> Char (Char.chr(int_of_string(list_to_string('0'::'x'::tl))))) in
 
       let char_final = disj char_hex char_normal in
       char_final s;;

(***************************************************************************************************)
(******************************************** String Parser ****************************************)
(***************************************************************************************************)
(*⟨String⟩ ⟨StringChar⟩ *)
(*⟨StringChar⟩::= ⟨StringLiteralChar⟩ | ⟨StringMetaChar⟩*)
(*| ⟨StringHexChar⟩*)

let nt_meta_char= 
  let nt_quote = (word_ci "\\\"")     in                                               
  let nt_backslash = (word_ci "\\\\") in
  let nt_tab = (word_ci "\\t")       in 
  let nt_page = (word_ci "\\f")      in  
  let nt_newline = (word_ci "\\n")   in
  let nt_return = (word_ci "\\r")   in
  let nt_backslash =  pack nt_backslash (fun ch -> Char.chr 92) in
  let nt_quote =  pack nt_quote (fun ch -> Char.chr 34)         in
  let nt_tab =  pack nt_tab (fun ch -> Char.chr 9)              in
  let nt_page =  pack nt_page (fun ch -> Char.chr 12)           in
  let nt_newline =  pack nt_newline (fun ch -> Char.chr 10)     in
  let nt_return =  pack nt_return (fun ch -> Char.chr 13)       in

  disj_list [nt_quote;nt_backslash;nt_tab;nt_page;nt_newline;nt_return;nt_any];;

let nt_prefix = (char '\"');; 
let nt_postfix = (char '\"');;

(* change (fun (hd,(tl,';') for warnings *)
let nt_string s =
  let nt_hex_prefix = word_ci "\\x"  in 
  let nt_string_hex = caten nt_hex_prefix (caten (plus nt_hex_digit)  (char ';')) in
  let nt_string_hex = pack nt_string_hex (fun (hd,(tl,_)) -> Char.chr(int_of_string(list_to_string('0'::'x'::tl)))) in
  let nt_read_str = disj nt_string_hex nt_meta_char in
  let nt_read_str = diff nt_read_str nt_prefix in
  let nt_read_str = star(nt_read_str) in
  let nt_extract_str = caten nt_postfix (caten nt_read_str nt_postfix) in
  let nt_extract_str = pack nt_extract_str (
  fun (_,( s, _)) -> String (list_to_string s)) in 
  nt_extract_str s

(***************************************************************************************************)
(******************************************** Symbol Parser ****************************************)
(***************************************************************************************************)

let nt_symbol s = 
  let nt_letter = range_ci 'a' 'z' in
  let nt_punctuation = one_of "!$^*-_=+<>/?:" in 
  
  let nt_symbol_helper = disj_list [nt_letter; nt_digit; nt_punctuation] in 
  let nt_symbol_helper = plus (nt_symbol_helper) in
  let nt_symbol_helper = pack nt_symbol_helper (fun s -> Symbol (list_to_string (List.map lowercase_ascii s) )) in
  (*convert to small letter*)
  nt_symbol_helper s



 (***************************************************************************************************)
(******************************************** Bool Parser ******************************************)
(***********************************************************************************************) 
let nt_bool s = 
  let bool_true = pack (word_ci "#t") (fun ch -> Bool true )in
  let bool_false = pack (word_ci "#f" ) (fun ch -> Bool false ) in
      let bool_help =  disj bool_true bool_false  in
      let bool_help = not_followed_by bool_help nt_symbol in
      bool_help s 

  (***************************************************************************************************)
  (******************************************** Number Parser ****************************************)
  (***************************************************************************************************)
  let nt_sign = disj (char '-') (char '+');;
  let nt_dot = char '.';;
  let nt_num_hex_prefix = (word_ci "#x");;

  (* three nt_helpers to do a part of the process in order to use that part in the scientific_notation *)
  
  let nt_reg_int_helper = pack (caten (maybe nt_sign) (plus (nt_digit)))
                (fun (hd,tl) -> match hd with
                | None | Some '+'    -> tl                   
                | Some '-'           -> '-'::tl
                | _                  -> raise X_nt_reg_int_helper);; 
  
  let nt_hex_int_helper = pack (caten (caten (nt_num_hex_prefix ) (maybe nt_sign)) (plus (nt_hex_digit)))
                (fun  ((prefix,sign),num) -> match sign with
                | None | Some '+'    -> int_of_string(list_to_string('0'::'x'::num))
                | Some '-'           -> -int_of_string(list_to_string('0'::'x'::num))
                | _                  -> raise X_nt_hex_int_helper);; 
                
  let nt_hex_float_helper = pack (caten (caten (nt_num_hex_prefix ) (maybe nt_sign)) (plus (nt_hex_digit)))
                (fun  ((prefix,sign),num) -> match sign with
                | None | Some '+'    -> (list_to_string('0'::'x'::num))
                | Some '-'           -> ("-"^(list_to_string('0'::'x'::num))) 
                | _                  -> raise X_nt_hex_float_helper_error);;
  
  let nt_reg_float_helper = pack (caten (caten nt_reg_int_helper nt_dot) (plus (nt_digit))) 
  (fun ((natural,dot),rest) ->
  string_to_list(list_to_string natural ^ "." ^ list_to_string rest));; 
  
  let nt_reg_int = pack nt_reg_int_helper 
  (fun (list_int)      -> Number(Int (int_of_string(list_to_string(list_int)))));;
  
  let nt_hex_int = pack nt_hex_int_helper
  (fun (int)           -> Number(Int (int)));;
  
  let nt_reg_float = pack nt_reg_float_helper 
  (fun (string_float)  -> Number(Float(float_of_string(list_to_string string_float))));;
  
  let nt_hex_float = pack (caten (caten nt_hex_float_helper nt_dot) (plus (nt_hex_digit))) 
  (fun ((natural,dot),rest) ->
  Number(Float(float_of_string (natural ^ "." ^ (list_to_string rest)))));;
  
  let nt_scientific_notation = pack (caten (caten (disj nt_reg_float_helper nt_reg_int_helper) (word_ci "e")) nt_reg_int_helper)
  (fun ((first,e),second)  -> Number(Float(float_of_string (list_to_string(List.concat[first;e;second])))));;
  
  
  let nt_num = disj_list [nt_scientific_notation;nt_hex_float;nt_hex_int; nt_reg_float; nt_reg_int];;

  let nt_number = pack (not_followed_by nt_num nt_symbol) (fun (a) -> a) (*FIXME: bug after test*)
      
  
              
(***************************************************************************************************)
(******************************************** Sexpr Parser *****************************************)
(***************************************************************************************************)

let rec nt_sexpr s = 
  let nt_sexpr_help = disj_list 
  [f nt_bool;f nt_char ; f nt_number ;f nt_string; f nt_nil; f nt_list; f nt_dotted_list; 
  f nt_symbol; f nt_vector; f nt_quoted; f nt_qquoted; f nt_unquoted_spliced; f nt_unquoted; 
  f nt_three_dot; f nt_inside_threedot_dis] in 

  nt_sexpr_help s

(* spaces & comments handling *)
and f parser =
  let nt_line_comment = caten (char ';') (caten (star (diff nt_any (char '\n'))) (char '\n')) in
  let nt_line_comment = pack nt_line_comment (fun _-> ' ') in
  let nt_sexp_comment = caten (word "#;") nt_sexpr in
  let nt_sexp_comment = pack nt_sexp_comment (fun _-> ' ') in
  let nt_comment = disj nt_line_comment nt_sexp_comment in
  let nt_skip_star = star (disj nt_whitespace nt_comment) in
  let nt_skiper = caten nt_skip_star (caten parser nt_skip_star) in
  let nt_skiper = pack nt_skiper (fun (_,(exp,_)) -> exp) in

  nt_skiper
(***************************************************************************************************)
(******************************************** Nil Parser *******************************************)
(***************************************************************************************************)


and nt_nil s = 
  let nt_line_comment = caten (char ';') (caten (star (diff nt_any (char '\n'))) (char '\n')) in
  let nt_line_comment = pack nt_line_comment (fun _-> ' ') in
  let nt_sexp_comment = caten (word "#;") nt_sexpr in
  let nt_sexp_comment = pack nt_sexp_comment (fun _-> ' ') in
  let nt_comment = disj nt_line_comment nt_sexp_comment in

  let nt_lparen = char '(' in 
  let nt_rparen = char ')' in
  let spaces = star (disj nt_whitespace nt_comment) in 
  let nil = caten (caten nt_lparen spaces) nt_rparen in
  let nil = pack nil (fun ((l, s), r) -> Nil) in

  nil s
(***************************************************************************************************)
(******************************************** List Parsers *****************************************)
(***************************************************************************************************)
(* Proper list *)
and nt_list s = 
  let nt_list_help = disj
    (caten nt_lparen (caten (star nt_sexpr) nt_rparen) )
    (caten nt_sq_lparen (caten (star nt_sexpr) nt_sq_rparen) ) in
  let nt_list_help = pack nt_list_help (fun (_,(exprs,_)) -> 
  List.fold_right (fun a b -> Pair (a,b)) exprs Nil) in
  nt_list_help s

(* Improper list *)
and nt_dotted_list s = 
  let nt_dotted_list_help = disj
  (caten nt_lparen (caten (plus nt_sexpr) (caten (char '.') (caten nt_sexpr nt_rparen)))) 
  (caten nt_sq_lparen (caten (plus nt_sexpr) (caten (char '.') (caten nt_sexpr nt_sq_rparen)))) 
  in let nt_dotted_list_help = pack nt_dotted_list_help (fun (_,(exprs,(_,(last_exp,_)))) ->
  List.fold_right (fun a b -> Pair (a,b)) exprs last_exp) in
  nt_dotted_list_help s


(* Parentheses completion support *)
and nt_three_dot s = 
  let nt_helper = caten  nt_inside_threedot_dis nt_close_all in
  let nt_packed = pack nt_helper (fun (s,_) ->   s ) in
  nt_packed s

and nt_inside_threedot_dis s = 
  let nt_dis = disj nt_threedot_Dot nt_threedot_List_  in
  nt_dis s

and nt_threedot_List_ s = 
  let nt_dis = disj (diff nt_sexpr nt_three_dot) nt_inside_threedot_dis in
  let nt_hd = caten nt_open  (star (nt_dis)) in
  let nt_rest = caten  nt_hd (maybe nt_close) in
  let nt_packed = pack nt_rest (fun ((_,s_list),_) -> List.fold_right (fun a b -> Pair(a,b)) s_list Nil) in
  nt_packed  s

(* same unless we have a dot - spacial care *)
and nt_threedot_Dot s = 
  let nt_dis = disj (diff nt_sexpr nt_three_dot) nt_inside_threedot_dis in
  let nt_hd = caten (caten nt_open  (star (nt_dis))) nt_dot in
  let nt_rest  = caten (caten nt_hd  nt_dis ) (maybe nt_close) in
  let nt_packed = pack nt_rest (fun ((((_,s_list),_) , s) , _) -> List.fold_right (fun a b -> Pair(a,b)) s_list s) in
  nt_packed s


    
(***************************************************************************************************)
(******************************************** Vector Parser ****************************************)
(***************************************************************************************************)

and nt_vector s =
  let nt_vector_help = caten (char '#') (caten nt_lparen (caten (star nt_sexpr) nt_rparen)) in
  let nt_vector_help = pack nt_vector_help (fun (_,(_,(exprs,_))) -> Vector exprs) in
  nt_vector_help s

(***************************************************************************************************)
(******************************************** Quote-like Parsers ***********************************)
(***************************************************************************************************)
(* ⟨Quoted⟩::=′⟨Sexpr⟩ *)
and nt_quoted s = 
  let nt_quoted_help = caten (word "'") nt_sexpr in
  let nt_quoted_help = pack nt_quoted_help 
        (fun (_,expr) -> Pair((Symbol "quote"),(Pair (expr,Nil)))) in
        nt_quoted_help s

(* ⟨QQuoted⟩::=‘⟨Sexpr⟩ *)
and nt_qquoted s = 
  let nt_qquoted_help = caten (word "`") nt_sexpr in
  let nt_qquoted_help = pack nt_qquoted_help 
        (fun (_,expr) -> Pair((Symbol "quasiquote"),(Pair (expr,Nil)))) in
        nt_qquoted_help s

(* ⟨UnquotedSpliced⟩::=;@⟨Sexpr⟩ *)
and nt_unquoted_spliced s = 
  let nt_unquoted_spliced = caten (word ",@") nt_sexpr in
  let nt_unquoted_spliced = pack nt_unquoted_spliced 
        (fun (_,expr) -> Pair((Symbol "unquote-splicing"),(Pair (expr,Nil)))) in
        nt_unquoted_spliced s
  
(* ⟨Unquoted⟩::=;⟨Sexpr⟩ *)
and nt_unquoted s = 
  let nt_unquoted_help = not_followed_by (caten (word ",") nt_sexpr) (char '*') in
  let nt_unquoted_help = pack nt_unquoted_help 
        (fun (_,expr) -> Pair((Symbol "unquote"),(Pair (expr,Nil)))) in
         nt_unquoted_help s;;


(***************************************************************************************************)
(***************************************************************************************************)

  module Reader: sig
    val read_sexpr : string -> sexpr
    val read_sexprs : string -> sexpr list
  end
  = struct
    let normalize_scheme_symbol str =
      let s = string_to_list str in
      if (andmap
      (fun ch -> (ch = (lowercase_ascii ch)))
      s) then str
      else Printf.sprintf "|%s|" str;;

      let read_sexpr string = 
        let (e,_) = nt_sexpr (string_to_list string)  in
        e;;
      let read_sexprs_helper string = 
        let nt = caten nt_sexpr (star nt_sexpr) in
        let nt = pack  nt (fun (a,b) -> a::b) in
        let (e,_) = nt (string_to_list string) in 
        e;;
      let read_sexprs string = 
        if (string = "") then ([])
        else (read_sexprs_helper string) ;;  
                
      end;; (* struct Reader *) 
      
           
      