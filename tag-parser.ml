(* tag-parser.ml
* A compiler from Scheme to CISC
*
 * Programmers: Sagiv Nethanel & Eran Levav, 2018
*)

#use "reader.ml";;
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;


let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
       | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
       (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
       | Applic(e1, args1), Applic(e2, args2) ->
       (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
       | _ -> false;;
       
       
       exception X_syntax_error;;
       
       
       module type TAG_PARSER = sig
        val tag_parse_expression : sexpr -> expr
        val tag_parse_expressions : sexpr list -> expr list
        
        end;; (* signature TAG_PARSER *)
        
        module Tag_Parser : TAG_PARSER = struct
          
          let reserved_word_list =
            ["and"; "begin"; "cond"; "define"; "else";
            "if"; "lambda"; "let"; "let*"; "letrec"; "or";
            "quasiquote"; "quote"; "set!"; "unquote";
            "unquote-splicing"];;
            
            (* work on the tag parser starts here *)
            
(***************************************************************************************************)
(******************************************** Assignment 2  ****************************************)
(***************************************************************************************************) 

(* check if the lambda match is simple by serching the nil in the end *)
let rec lambda_is_simple s = match s with
      | Nil                       -> true
      | Pair(Symbol first,Nil)    -> true
      | Pair(Symbol first,second) -> lambda_is_simple second
      | _                         -> false;; 
(**************************************************************************************************)
let rec symbol_to_string s = match s with
      | Nil                       -> []
      | Pair(Symbol first,Nil)    -> [first]
      | Pair(Symbol first,second) -> let unique_args = (symbol_to_string second) in
                                    if (List.mem first unique_args) 
                                    then raise X_syntax_error
                                    else first::unique_args
      | _                         -> raise X_syntax_error;;
(**************************************************************************************************)
let rec symbol_end_with_dot_to_string s = match s with
      | Nil                           -> []
      | Pair(Symbol first,Symbol vs)  ->  if (vs=first) 
                                          then raise X_syntax_error 
                                          else [vs;first]
      | Pair(Symbol first,second) -> let unique_args = (symbol_end_with_dot_to_string second) in
                                          if (List.mem first unique_args) 
                                          then raise X_syntax_error
                                          else (List.hd unique_args) :: first:: (List.tl unique_args)
      | _                         -> raise X_syntax_error;;       
(**************************************************************************************************)
let rec sexprs_to_list s = match s with
      | Nil                       -> []
      | Pair(first,Nil)           -> [first]
      | Pair(first,second)        ->  first::(sexprs_to_list second)
      | _                         -> raise X_syntax_error

(**************************************************************************************************)
let rec letrec_arglist ribs = match ribs with
      | Nil                                  -> Nil
      | Pair(Pair(Symbol name,expr),rest)    -> Pair(Pair(Symbol name, Symbol "whatever"), letrec_arglist rest)
      | _                                    -> raise X_syntax_error

(**************************************************************************************************)
let check_no_reserve_word x = if (List.mem x reserved_word_list)
                              then raise X_syntax_error
                              else Var (x);;
(**************************************************************************************************)
let car = function 
      | Pair(a,b) -> a
      | _ ->raise X_syntax_error

let cdr = function 
      | Pair(a,Pair(b,Nil)) -> b
      | Pair(a,b) -> b
      | _->raise X_syntax_error                              

(**************************************************************************************************)

(**************************************************************************************************)
let rec tag_parse = function

(***************************************** Constants **********************************************)

      | Pair(Symbol("quote"), Pair(x, Nil))   -> Const(Sexpr(x))
      | Pair(Symbol("unquote"), Pair(x, Nil)) -> Const(Sexpr(x))
      | Number(x)                             -> Const(Sexpr(Number(x)))
      | Bool(x)                               -> Const(Sexpr(Bool(x)))
      | String(x)                             -> Const(Sexpr(String(x)))
      | Char(x)                               -> Const(Sexpr(Char(x)))
      | Nil                                   -> Const(Sexpr(Nil))

(**************************************** Conditionals ********************************************)  

      | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) ->
                        If(tag_parse test, tag_parse dit, tag_parse dif)

      | Pair(Symbol("if"), Pair(test, Pair(dit, Nil)))            ->
                        If(tag_parse test, tag_parse dit, Const(Void)) 

(******************************************* Lambda ***********************************************)


      (*lambda vardict - special care*)
      
      | Pair(Symbol("lambda"), Pair(Symbol vs, body)) ->
            let body = tag_parse (Pair (Symbol "begin", body)) in
            if (body=Const(Void)) (* Check body is not empty *)
            then raise X_syntax_error  
            else LambdaOpt ([],vs ,body)

      | Pair(Symbol("lambda"),Pair(arglist, body)) ->
            let body = tag_parse (Pair (Symbol "begin", body)) in
            if (body=Const(Void)) (* Check body is not empty *)
            then raise X_syntax_error 
            else
                  if (lambda_is_simple arglist) 
                  then (let arglist = symbol_to_string arglist in 
                        LambdaSimple (arglist, body))
                  else (let arglist = symbol_end_with_dot_to_string arglist in 
                        LambdaOpt (List.tl arglist,List.hd arglist,body))

(***************************************** Disjunctions *******************************************)

      | Pair (Symbol ("or"), Nil)                     -> Const(Sexpr(Bool false)) (*#f is the unit element of or, by definition *) 
      | Pair (Symbol ("or"), Pair (one_element, Nil)) -> tag_parse one_element
      | Pair (Symbol ("or"), Pair (first, rest))      -> 
                      let sexpr_list = first::(sexprs_to_list rest) in 
                      Or (List.map tag_parse sexpr_list)
                              
(***************************************** Definitions ********************************************) 

      | Pair (Symbol("define"), Pair (Symbol var, Pair (expr, Nil))) ->
                       Def (check_no_reserve_word var, tag_parse expr)

      | Pair (Symbol("define"), Pair (Pair (var, arglist), expr))    ->
                       tag_parse (Pair (Symbol "define", Pair (var, Pair (Pair (Symbol "lambda", Pair (arglist, expr)), Nil))))

(******************************************* Sequences ********************************************)

      | Pair (Symbol("begin"), Nil)                ->  Const(Void)
      | Pair (Symbol("begin"), Pair(x,Nil)) -> tag_parse x
      | Pair (Symbol("begin"), Pair (first, rest)) ->  (*Like or handle*)
           let sexpr_list = first::(sexprs_to_list rest) in 
           Seq (List.map tag_parse sexpr_list)

(******************************************* Assignments ******************************************)

      | Pair (Symbol("set!"), Pair(Symbol expr_name ,Pair(expr_new_val,Nil))) -> 
          Set (check_no_reserve_word expr_name, tag_parse expr_new_val)

(******************************************** Variables *******************************************) 

      | Symbol(x)                                  -> check_no_reserve_word x    


(*********************************************** And **********************************************)      


      | Pair (Symbol ("and"), Nil)                     -> Const(Sexpr(Bool true)) (*#t by definition *) 
      | Pair (Symbol ("and"), Pair (one_element, Nil)) -> tag_parse one_element
      | Pair (Symbol ("and"), Pair(first,rest))        -> tag_parse (Pair(Symbol("if"),Pair(first, Pair(Pair(Symbol("and"),rest),Pair(Bool false, Nil)))))
                                                             
(*********************************************** Let **********************************************)   

(*                                          The empty let                                         *)
      | Pair (Symbol "let", Pair(Nil,body)) -> 
                              Applic(tag_parse (Pair(Symbol("lambda"), Pair (Nil, body))),[])

(*                                            Regular let                                         *)
      | Pair (Symbol "let", Pair(Pair(rib,ribs),body)) -> 

            let params = (List.fold_right 
                  (fun a b -> Pair (a,b))
                  (List.map car (rib::(sexprs_to_list ribs)))
                  Nil) in

            let vals = (List.fold_right 
                  (fun a b -> Pair (a,b))
                  (List.map cdr (rib::(sexprs_to_list ribs)))
                  Nil) in

                     tag_parse (Pair(Pair(Symbol("lambda"),Pair(params, body)), vals))

(********************************************** Let Star ******************************************) 

(*                                         The empty let star                                     *)
      | Pair (Symbol "let*", Pair(Nil,body)) -> 
                              tag_parse (Pair (Symbol "let", Pair(Nil,body)))


(*                                          One var let star                                      *)
      | Pair (Symbol "let*", Pair(Pair(one_rib,Nil),body)) -> 
                              tag_parse (Pair (Symbol "let",Pair(Pair(one_rib,Nil),body)))

(*                                         Regular let star                                      *)
      | Pair (Symbol "let*", Pair(Pair(rib1,rest),body)) ->       
                              tag_parse(Pair(Symbol "let", Pair(Pair(rib1,Nil), Pair(Pair(Symbol "let*", Pair(rest,body)), Nil))))


(********************************************* Letrec ***********************************************)

(*                                        The empty letrec                                          *)
      | Pair (Symbol "letrec", Pair(Nil,body)) -> 
                   Applic (tag_parse (Pair(Symbol "lambda", Pair (Nil,body))), [])

(*                                         One var letrec                                           *)
      
      | Pair (Symbol "letrec", Pair(Pair(Pair(rib,Nil),Nil),body)) -> 
                   tag_parse (Pair (Symbol "let", Pair(Pair(rib,Nil),body)))

(*                                         Regular letrec                                           *)
      | Pair (Symbol "letrec", Pair(Pair(rib,ribs),body)) ->
                  let new_body = Pair(Symbol "begin",
                  (List.fold_right 
                  (fun a b -> Pair (a,b)) 

                  (List.map 
                  (fun rib -> Pair(Symbol "set!",rib))
                  (sexprs_to_list (Pair(rib,ribs))))  body)) in

                  let new_rib =  Pair(car rib,Pair(Symbol("quote"), Pair(Symbol "whatever", Nil)) ) in

                  let new_ribs =  (List.fold_right 
                  (fun a b -> Pair (a,b)) 

                  (List.map 
                  (fun rib -> Pair(car rib,Pair(Symbol("quote"), Pair(Symbol "whatever", Nil)) ))
                  (sexprs_to_list ribs))
                  Nil
                  ) in

                  tag_parse (Pair (Symbol "let", Pair(Pair(new_rib,new_ribs),Pair(new_body,Nil))))

(******************************************** Quasiquote ********************************************)

      | Pair((Symbol "quasiquote"),(Pair (expr,Nil))) ->(
            match expr with
            | Pair((Symbol "unquote"),(Pair (e,Nil))) -> tag_parse e
            | Pair((Symbol "unquote-splicing"),(Pair (e,Nil))) -> raise X_syntax_error
            | Nil -> tag_parse (Pair(Symbol("quote"), Pair(Nil, Nil)))
            | Symbol(e) -> tag_parse (Pair(Symbol("quote"), Pair(Symbol(e), Nil)))
            | String(e) -> tag_parse (Pair(Symbol("quote"), Pair(String(e), Nil)))
            | Char(e) -> tag_parse (Pair(Symbol("quote"), Pair(Char(e), Nil)))
            | Number(e) -> tag_parse (Pair(Symbol("quote"), Pair(Number(e), Nil)))
            | Vector(elements) -> 
                        let taged_elements =
                              (List.fold_right 
                              (fun a b -> Pair (a,b)) 
                              (List.map 
                                    (fun x -> (Pair(Symbol "quasiquote",(Pair (x,Nil)))))
                                    elements)
                              Nil)
                              in                 tag_parse (Pair (Symbol "vector", taged_elements))


            | Pair(Pair(Symbol "unquote-splicing",Pair(a,Nil)),b) -> 
                  tag_parse (Pair(Symbol "append",Pair(a,Pair(Pair(Symbol "quasiquote",Pair(b,Nil)),Nil))))

            | Pair(a,Pair(Symbol "unquote-splicing",Pair(b,Nil))) ->
                  tag_parse (Pair(Symbol "cons",Pair(Pair(Symbol "quasiquote",Pair(a,Nil)),Pair(b,Nil))))


            | Pair(a,b) -> 
                  let a = Pair(Symbol "quasiquote",Pair(a,Nil)) in
                  let b = Pair(Symbol "quasiquote",Pair(b,Nil)) in
                  tag_parse (Pair(Symbol "cons",Pair(a,Pair(b,Nil))))

            | _-> raise X_syntax_error)

(*********************************************** Cond **********************************************)

      | Pair(Symbol "cond", ribs) -> (
            match ribs with

            | Pair(Pair(Symbol "else", body),Nil)                   -> tag_parse (Pair (Symbol("begin"), body))
       

            | Pair(Pair(expr, Pair(Symbol "=>",exprf)), Nil) -> tag_parse(
                  Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(expr, Nil)), 
                  Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, exprf)), Nil)), Nil)), 
                  Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), 
                  Pair(Symbol "value", Nil)), Nil))), Nil))))

            | Pair(Pair(expr, Pair(Symbol "=>",exprf)), rest) -> tag_parse(
                  Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(expr, Nil)),
                  Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil,exprf)), Nil)),
                  Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(Pair(Symbol "cond", rest), Nil))), Nil)), Nil))), Pair(Pair(Symbol "if", Pair(Symbol "value",
                  Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil))) )    

            | Pair(Pair(test,body),Nil) -> tag_parse (Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol "begin",body), Nil))))

            | Pair(Pair(test,body),rest) -> tag_parse (Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol "begin",body), Pair(Pair(Symbol "cond", rest), Nil)))))
            
            | _ -> raise X_syntax_error)
      

(**********************************************************Applications:*********************************************)
      | Pair(expr, expr_list) -> Applic (tag_parse expr, List.map tag_parse (sexprs_to_list expr_list)) 

      | _                                              -> raise X_syntax_error;;
       

(******************************************** end Assignment 2 *************************************)
(***************************************************************************************************)   

let tag_parse_expression sexpr = tag_parse sexpr;;
let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;

(***************************************************************************************************)   
end;; (* struct Tag_Parser *)