(* semantic-analyser.ml
 * A compiler from Scheme to CISC
 *
 * Programmers: Sagiv Nethanel & Eran Levav, 2018
 *)
(* ************************************************************************************************** *)
(* ************************************************************************************************** *)
#use "tag-parser.ml";;
open Tag_Parser;;
open Reader;;

(* ************************************************************************************************** *)
(* ************************************************************************************************** *)
type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;
(* ************************************************************************************************** *)
type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;
(* ************************************************************************************************** *)
let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | Box'(_), Box'(_) -> true
  | BoxGet'(_), BoxGet'(_) -> true
  | BoxSet'(_, v1), BoxSet'(_, v2) -> expr'_eq v1 v2 
  | _ -> false;;
  
(* ************************************************************************************************** *)
exception X_syntax_error;;
exception X_Error;;
exception X_Debug;;
(* ************************************************************************************************** *)
(* **************************************** Globals ************************************************* *)
(* ************************************************************************************************** *)
let env = ref [];;
let box_var_copies = ref 0;;
let box_read_occ =   ref [];; 
let box_write_occ = ref [];;
(* ************************************************************************************************** *)
(* ************************************************************************************************** *)
module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;
(* ************************************************************************************************** *)
module Semantics : SEMANTICS = struct
(* ************************************************************************************************** *)
(* *************************************** Lexical Addresses **************************************** *)
(* ************************************************************************************************** *)
let rec lexical_addresses_rec e =
     match e with
      | Const(exp)                          -> Const' (exp)
      | Seq (exps)                          -> Seq' (List.map lexical_addresses_rec exps) 
      | If (test,dit,dif)                   -> If' (lexical_addresses_rec test , lexical_addresses_rec dit ,  lexical_addresses_rec dif)  
      | Set (var,exp)                       -> Set' (lexical_addresses_rec var, lexical_addresses_rec exp)
      | Def (var,exp)                       -> Def' (lexical_addresses_rec var, lexical_addresses_rec exp)
      | Or (exps)                           -> Or' (List.map lexical_addresses_rec exps)
      | Applic (op, rands)                  -> Applic' (lexical_addresses_rec op, List.map lexical_addresses_rec rands)
      | LambdaSimple(vars, body)            -> env := (vars::!env) ;  (*Update our env with new vars *)
                                               let lambda = LambdaSimple'(vars ,lexical_addresses_rec body) in (*The LambdaOpt onstruction is delayed *)
                                              (*Now we can restore the env after the scope ends and return the lambda*)
                                               env := (List.tl !env) ;
                                               lambda 
      | LambdaOpt (vars,opt_vals, body)      -> env := ((vars@[opt_vals])::!env) ;
                                               let lambda = LambdaOpt'(vars ,opt_vals,lexical_addresses_rec body) in
                                               env := (List.tl !env) ;
                                               lambda 
      | Var(var)                            -> find_var var !env 
      (* | _                                   -> no need  *)
(* ************************************************************************************************** *)
and     find_var var env = find_var_helper var env (-1)
(* ************************************************************************************************** *)
and     find_var_helper var env maj =
    match env with
      | []                ->    Var'(VarFree var)
      | first::rest       ->    if (List.mem var first) 
                                then (if(maj = -1) 
                                      then Var'(VarParam(var,(indx_of var first))) 
                                      else Var'(VarBound(var,maj,(indx_of var first)))) 
                                else find_var_helper var (List.tl env) (maj+1)

    (* | _ -> raise X_syntax_error  no need  *)
(* ************************************************************************************************** *)
and     indx_of element lst = indx_of_helper element lst 0       
(* ************************************************************************************************** *)
and     indx_of_helper element lst pos =

  if (element = (List.hd lst))
    then  pos
    else indx_of_helper element (List.tl lst) (pos+1)
(* ************************************************************************************************** *)
(* ***************************************** Tail Calls ********************************************* *)
(* ************************************************************************************************** *)
and tail_calls_rec e_tag is_tail_pos = 
      match e_tag with

      | Const' (exp)                      -> e_tag
      | Seq' (exps)                       -> Seq' (tail_calls_rec_map exps is_tail_pos) 
      | If' (test,dit,dif)                -> If'  (tail_calls_rec test false,tail_calls_rec dit is_tail_pos,tail_calls_rec dif is_tail_pos)  
      | Set' (var,exp)                    -> Set' (var,tail_calls_rec exp false)
      | Def' (var,exp)                    -> Def' (var,tail_calls_rec exp false)
      | Or' (exps)                        -> Or'  (tail_calls_rec_map exps is_tail_pos)
      | Applic' (op, rands)               -> if (is_tail_pos) 
                                             then ApplicTP'(tail_calls_rec op false, tail_calls_rec_map rands false )
                                             else Applic' (tail_calls_rec op false, tail_calls_rec_map rands false )
      | LambdaSimple'(vars, body)         -> LambdaSimple'(vars, tail_calls_rec body true) 
      | LambdaOpt'(vars,opt_vals, body)   -> LambdaOpt'(vars,opt_vals, tail_calls_rec body true)
      | Var'(var)                         -> e_tag  
      | _                                 -> raise X_Error   
(* ************************************************************************************************** *)
and tail_calls_rec_map exps is_tail_pos =
    if ((List.length exps) = 0)
    then []
    else if ((List.length exps) = 1)
         then [tail_calls_rec (List.hd exps) is_tail_pos] 
         else tail_calls_rec (List.hd exps) false :: (tail_calls_rec_map (List.tl exps) is_tail_pos)
   
(* ************************************************************************************************** *)
(* ******************************************* Box Set ********************************************** *)
(* ************************************************************************************************** *)
and box_set_rec e_tag = 

      match e_tag with
      | Const' (exp)                      -> e_tag
      | BoxSet'(var,exp)                  -> BoxSet'(var,box_set_rec exp)
      | BoxGet'   _                       -> e_tag
      | Box'      _                       -> e_tag
      | Seq' (exps)                       -> Seq'(box_set_rec_map exps)
      | If' (test,dit,dif)                -> If'(box_set_rec test,box_set_rec dit,box_set_rec dif)
      | Def' (var,exp)                    -> Def'(var,box_set_rec exp)
      | Or' (exps)                        -> Or'(box_set_rec_map exps)
      | Applic' (op, rands)               -> Applic'(box_set_rec op, box_set_rec_map rands)
      | ApplicTP' (op, rands)             -> ApplicTP'(box_set_rec op, box_set_rec_map rands)
      | Var'(var)                         -> e_tag
      | Set' (var,exp)                    -> Set'(var,box_set_rec exp)

      | LambdaSimple'(vars, body)         ->  let new_body = ref body in 
                                              let set_get_seq = ref [] in 

                                              for i = 0 to (List.length vars) -1
                                              do
                                                box_var_copies := 0; (* Init *)
                                                let var = List.nth vars i in
                                                if (box_should_wrap var !new_body)
                                                  then  (new_body    := box_wrap var !new_body ;
                                                         set_get_seq :=   Set'(Var'(VarParam(var,indx_of var vars)),
                                                                          Box'(VarParam(var,indx_of var vars)))
                                                                          :: !set_get_seq ;)
                                              done  ;
                                             if (!set_get_seq = []) 
                                             then LambdaSimple'(vars,(box_set_rec !new_body))
                                             else LambdaSimple'(vars,(box_set_rec (Seq'((List.rev !set_get_seq) @ [!new_body]))))


      | LambdaOpt'(vars,opt_vals, body)    -> let new_body = ref body in 
                                              let set_get_seq = ref [] in 
                                              let all_vars = ref (vars@[opt_vals]) in
                                              for i = 0 to (List.length !all_vars) -1
                                              do
                                                box_var_copies := 0; (* Init *)
                                                let var = List.nth !all_vars i in
                                                if (box_should_wrap var !new_body)
                                                  then  (new_body    := box_wrap var !new_body ;
                                                         set_get_seq :=   Set'(Var'(VarParam(var,indx_of var !all_vars)),
                                                                          Box'(VarParam(var,indx_of var !all_vars)))
                                                                          :: !set_get_seq ;)
                                              done  ;
                                             if (!set_get_seq = []) 
                                             then LambdaOpt'(vars,opt_vals,(box_set_rec !new_body))
                                             else LambdaOpt'(vars,opt_vals,(box_set_rec (Seq'((List.rev !set_get_seq) @ [!new_body]))))

      (* | _                                 -> no need  *)
(* ************************************************************************************************** *)
and     box_set_rec_map exps =
    if ((List.length exps) = 0)
    then []
    else box_set_rec (List.hd exps) :: (box_set_rec_map (List.tl exps))

(* ************************************************************************************************** *)
and     var_tag_to_string var_tag =
    match var_tag with
      | Var'(VarFree(var)) -> var
      | Var'(VarParam(var,_)) -> var
      | Var'(VarBound(var,_,_)) -> var

      | _ -> raise X_Error
(* ************************************************************************************************** *)
and     box_should_wrap var_name body_to_check = 

  let is_on_stack = true in 
    (* fill read and write data structures *)
  box_find_read_write_occ var_name body_to_check is_on_stack;  
    (* check if should wrap *)
  let is_box_needed = (box_check_struct !box_read_occ !box_write_occ) in 
    (* clean structures for next var to check *)
  (* Printf.printf "*****************for debug**********************************";
  Printf.printf "%n\n" (List.hd !box_read_occ);  
  Printf.printf "%n\n" (List.hd !box_write_occ);   *)

  box_read_occ := [] ;
  box_write_occ := [] ;

  is_box_needed
(* ************************************************************************************************** *)
and     box_find_read_write_occ var_to_search expr is_on_stack =  

      match expr with 
      | Const' (exp)                           -> ()
      | BoxGet'   _                            -> ()
      | BoxSet'(var,exp)                       -> box_find_read_write_occ var_to_search exp is_on_stack
      | Box'      _                            -> ()
      | Seq' (exps)                            -> box_find_read_write_occ_map var_to_search exps is_on_stack

      | If' (test,dit,dif)                     -> box_find_read_write_occ var_to_search test is_on_stack;
                                                  box_find_read_write_occ var_to_search dit is_on_stack;
                                                  box_find_read_write_occ var_to_search dif is_on_stack;

      | Set' (var,exp)                         ->   box_find_read_write_occ var_to_search exp is_on_stack;
                                                    if (var_to_search = (var_tag_to_string var) )
                                                    then (if (is_on_stack)
                                                          then box_write_occ := (0::!box_write_occ)
                                                          else box_write_occ := (!box_var_copies::!box_write_occ))


      | Var'(var)                              ->   if (var_to_search = (var_tag_to_string expr) )
                                                    then (if (is_on_stack)
                                                          then box_read_occ := (0::!box_read_occ)
                                                          else box_read_occ := (!box_var_copies::!box_read_occ))

      | Def' (var,exp)                         -> ()

      | Or' (exps)                             -> box_find_read_write_occ_map var_to_search exps is_on_stack

      | Applic'(op,rands)                      -> box_find_read_write_occ var_to_search op is_on_stack;
                                                  box_find_read_write_occ_map var_to_search rands is_on_stack;

      | ApplicTP'(op,rands)                    -> box_find_read_write_occ var_to_search op is_on_stack;
                                                  box_find_read_write_occ_map var_to_search rands is_on_stack;
                                                    
      | LambdaSimple'(vars, body)              -> if (not (List.mem var_to_search vars))
                                                  then 
                                                    (
                                                      if (is_on_stack)
                                                        then box_var_copies := !box_var_copies+1;

                                                     box_find_read_write_occ var_to_search body false 
                                                    )
                                         
      | LambdaOpt'(vars,opt_vals, body)         -> if (not (List.mem var_to_search vars) && (var_to_search != opt_vals))
                                                  then 
                                                    (
                                                      if (is_on_stack)
                                                        then box_var_copies := !box_var_copies+1;

                                                     box_find_read_write_occ var_to_search body false
                                                    )
                                         
      (* | _                                      -> no need  *)
(* ************************************************************************************************** *)
and     box_find_read_write_occ_map var_to_search exps is_on_stack =
    if    ((List.length exps) = 0)
      then  ()
      else  
          (box_find_read_write_occ  var_to_search (List.hd exps) is_on_stack ;
          box_find_read_write_occ_map  var_to_search (List.tl exps) is_on_stack)
(* ************************************************************************************************** *)
and     box_check_struct box_read_occ box_write_occ = 
  match box_read_occ,box_write_occ with
   | [] , _ | _,[]           -> false
   | first_r::rest_r , first_w::rest_w -> if first_r != first_w
                                          then true
                                          else (box_check_struct   box_read_occ  rest_w 
                                            ||  box_check_struct   rest_r        box_write_occ)
(* ************************************************************************************************** *)
and     box_wrap var_to_wrap expr = 
  match expr with 
      | Const'(exp)                              -> expr
      | BoxGet'   _                              -> expr
      | BoxSet'(var,exp)                         -> BoxSet'(var,box_wrap var_to_wrap exp)
      | Box'      _                              -> expr

      | Seq' (exps)                             ->  Seq' (box_wrap_map var_to_wrap exps)

      | If' (test,dit,dif)                      -> If' (box_wrap var_to_wrap test,
                                                        box_wrap var_to_wrap dit,
                                                        box_wrap var_to_wrap dif)

      | Set' (var_tag ,exp)        (* Write *)      -> if ( var_to_wrap = (var_tag_to_string var_tag) )
                                                        then BoxSet'(var_tag_to_var var_tag ,box_wrap var_to_wrap exp)
                                                        else Set'(var_tag ,box_wrap var_to_wrap exp)

      | Var' (var)                  (* Read *)      -> if ( var_to_wrap = (var_tag_to_string expr) )
                                                          then BoxGet'(var)
                                                          else expr

      | Def' (var,exp)                         -> Def' ( var,(box_wrap      var_to_wrap   exp) )

      | Or' (exps)                             -> Or'        (box_wrap_map  var_to_wrap   exps)
  
      | Applic'(op,rands)                      -> Applic'   ((box_wrap      var_to_wrap   op),
                                                             (box_wrap_map  var_to_wrap   rands))

      | ApplicTP'(op,rands)                    -> ApplicTP' ((box_wrap      var_to_wrap   op    ),
                                                             (box_wrap_map  var_to_wrap   rands ))
                                                    
      | LambdaSimple'(vars, body)              -> 
            if (List.mem var_to_wrap vars)
              then LambdaSimple'(vars, body)
              else LambdaSimple'(vars, box_wrap var_to_wrap body )

      | LambdaOpt'(vars, opt_vals, body)        -> 
            if ((List.mem var_to_wrap vars) || (var_to_wrap == opt_vals) )
              then LambdaOpt'(vars,opt_vals, body)
              else LambdaOpt'(vars, opt_vals, box_wrap var_to_wrap body )


      (* | _                                      -> no need   *)
(* ************************************************************************************************** *)
and     var_tag_to_var var_tag = 
  match var_tag with
  | Var'(var) -> var
  | _ -> raise X_Error
(* ************************************************************************************************** *)
and     box_wrap_map var_to_wrap exps =
    if ((List.length exps) = 0)
    then []
    else box_wrap var_to_wrap (List.hd exps) :: (box_wrap_map var_to_wrap (List.tl exps))
(* ************************************************************************************************** *)
let     annotate_lexical_addresses e = lexical_addresses_rec e;;  
(* ************************************************************************************************** *)
let     annotate_tail_calls e = tail_calls_rec e false;;          
(* ************************************************************************************************** *)
let     box_set e = box_set_rec e;;
(* ************************************************************************************************** *)
let     run_semantics expr =
  box_set
     ( annotate_tail_calls  
       (annotate_lexical_addresses expr));;
(* ************************************************************************************************** *)
end;; (* struct Semantics *)