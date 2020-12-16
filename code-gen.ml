#use "semantic-analyser.ml";;
open Semantics;;
open Tag_Parser;;
open Reader;;

exception X_syntax_error;;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list (*TODO:   val make_consts_tbl : expr' list -> (constant * ('a * string)) list *)
  val make_fvars_tbl : expr' list -> (string * (int * string)) list           (*TODO:   val make_fvars_tbl : expr' list -> (string * 'a) list*)
  val generate : (constant * (int * string)) list -> (string * (int * string)) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

   (*generator of labels for assembly func*)
  let label_generator = ref (-1);;
  let label_maker label =  label_generator := !label_generator + 1 ;
                           Printf.sprintf("%s%d")  label !label_generator;;

 (*two functions that removing_duplicates*)
  let single_element_compare tl hd = if List.mem hd tl then tl else hd::tl 
  let removing_duplicates tbl_const = List.rev (List.fold_left single_element_compare [] tbl_const)

  let assembly_strings sexpr index = (* index only for debug *)
    match sexpr with 
      | Sexpr(Number(Int x))      -> Printf.sprintf("MAKE_LITERAL_INT(%d) ;offset is %d") x index
      | Sexpr(Number(Float x))    -> Printf.sprintf("MAKE_LITERAL_FLOAT(%f) ;offset is %d") x index 
      | Sexpr(Bool(false))        -> "MAKE_BOOL(0)"
      | Sexpr(Bool(true))         -> "MAKE_BOOL(1)"
      | Sexpr(String(x))          -> let list_of_chars = string_to_list x in
                                     let list_of_ascii = List.map Char.code list_of_chars in
                                     let final_string = String.concat ", " (List.map (fun x-> Printf.sprintf("%d") x) list_of_ascii)in
                                     "MAKE_LITERAL_STRING " ^ final_string
      | Sexpr(Char(x))            -> Printf.sprintf("MAKE_LITERAL_CHAR(%d) ;offset is %d") (Char.code x) index 
      | Sexpr(Nil)                -> "MAKE_NIL"
      | Void                      -> "MAKE_VOID" 
      | _                         -> "MAKE_Debbug"


  let rec size_of_the_constant sexpr = 
    match sexpr with
      | Sexpr(Number(x))          -> 9
      | Sexpr(Bool(x))            -> 2
      | Sexpr(String(x))          -> 9 + (String.length x)
      | Sexpr(Symbol(x))          -> 9
      | Sexpr(Char(x))            -> 2
      | Sexpr(Nil)                -> 1
      | Sexpr(Vector(list))       -> 9 + (8 * List.length list)
      | Void                      -> 1 
      | Sexpr(Pair(car,cdr))      -> 17


  let rec collect_the_sexprs asts tbl = 
   match asts with
      | Const' (exp)                      -> tbl@[exp]
      | BoxSet'(var,exp)                  -> collect_the_sexprs exp tbl
      | BoxGet'   _                       -> tbl
      | Box'      _                       -> tbl
      | Seq' (exps)                       -> let seq_tbl  = List.rev (List.fold_right (fun exp -> collect_the_sexprs exp) exps []) in
                                             tbl @ seq_tbl
      | If' (test,dit,dif)                -> let test_tbl = collect_the_sexprs test tbl      in
                                             let dit_tbl  = collect_the_sexprs dit test_tbl  in
                                             let dif_tbl  = collect_the_sexprs dif dit_tbl   in
                                             dif_tbl
      | Def' (var,exp)                    -> collect_the_sexprs exp tbl
      | Or' (exps)                        -> let or_tbl  = List.rev (List.fold_right (fun exp -> collect_the_sexprs exp) exps []) in
                                             tbl @ or_tbl
      | Applic' (op, rands)               -> let op_tbl = collect_the_sexprs op tbl in
                                             let applic_tbl =  List.rev (List.fold_right (fun exp -> collect_the_sexprs exp) rands []) in
                                             op_tbl @ applic_tbl
      | ApplicTP' (op, rands)             -> let op_tbl = collect_the_sexprs op tbl in 
                                             let applic_tbl = List.rev (List.fold_right (fun exp -> collect_the_sexprs exp) rands []) in 
                                             op_tbl @ applic_tbl
      | Var'(var)                         -> tbl
      | Set' (var,exp)                    -> collect_the_sexprs exp tbl
      | LambdaSimple'(vars, body)         -> collect_the_sexprs body tbl
      | LambdaOpt'(vars,opt_vals, body)   -> collect_the_sexprs body tbl

  let rec serch_for_all_sub_constants tbl_set = 
  	List.fold_left 
		(fun acc_list sexpr -> acc_list@serch_for_all_sub_constants_help sexpr acc_list) 
		[]
		tbl_set
	        									
  and serch_for_all_sub_constants_help sexpr acc_list = 
	  match sexpr with
      | Sexpr(Symbol exp)         -> 	Sexpr(String exp)::[sexpr]

      | Sexpr(Pair(car,cdr))      -> 	(serch_for_all_sub_constants_help (Sexpr(car)) acc_list)
                                @ 	(serch_for_all_sub_constants_help (Sexpr(cdr)) acc_list)
                                @	[sexpr]
                              
      | Sexpr(Vector(exprs))      ->  (List.fold_left 
                        (fun acc_list exp -> 
                          acc_list @serch_for_all_sub_constants_help (Sexpr(exp)) acc_list 
                        )
                        acc_list
                        exprs) @[sexpr]
      | _-> [sexpr]    

  let rec make_tupple_constants_table index tbl tbl_copy= 
    match tbl with 
      | []       -> []
      | hd::tail -> [(hd,(index,assembly_strings hd index))] @ make_tupple_constants_table (size_of_the_constant hd + index) tail tbl_copy
  
  let populate_constants_table tbl = make_tupple_constants_table 0 tbl ;;

  let rec make_consts_for_vector const_tbl vector_list = 
      match vector_list with
      | [] -> "" 
      | hd::tail -> let (offset,_) = List.assoc (Sexpr(hd)) const_tbl in
                  let ass_string = Printf.sprintf "const_tbl+%d" offset in
                  if ((List.length tail) = 0)
                  then ass_string ^ (make_consts_for_vector const_tbl tail)
                  else ass_string ^", " ^(make_consts_for_vector const_tbl tail)


  let rec make_final_tupple const_tbl origion_const_tbl=  
    match const_tbl with
      | []                                    -> []
      | (Sexpr(Symbol(x)), (i,_))::tail       -> let (offset,_) = List.assoc (Sexpr(String(x))) origion_const_tbl in
                                                 let ass_string = Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" offset in
                                                 [(Sexpr(Symbol(x)), (i,ass_string))]  @ make_final_tupple tail origion_const_tbl
      | (Sexpr(Pair(car,cdr)), (i,_))::tail   -> let (offset_car,_) = List.assoc (Sexpr(car)) origion_const_tbl in
                                                 let (offset_cdr,_) = List.assoc (Sexpr(cdr)) origion_const_tbl in
                                                 let ass_string = Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d,const_tbl+%d)" offset_car offset_cdr in
                                                 [(Sexpr(Pair(car,cdr)), (i,ass_string))]  @ make_final_tupple tail origion_const_tbl
      | (Sexpr(Vector(lst)), (i,_))::tail      -> let ass_string = "MAKE_LITERAL_VECTOR "  ^ (make_consts_for_vector origion_const_tbl lst)  in
                                                 [(Sexpr(Vector(lst)),(i,ass_string))]  @ make_final_tupple tail origion_const_tbl
      | hd::tail                               -> hd :: make_final_tupple tail origion_const_tbl


  let rec getting_free_vars asts tbl = 
   match asts with
      | Const' (exp)                      -> tbl
      | BoxSet'(var,exp)                  -> getting_free_vars exp tbl
      | BoxGet' _                         -> tbl
      | Box'    _                         -> tbl
      | Seq' (exps)                       -> let seq_tbl  = List.rev (List.fold_right (fun exp -> getting_free_vars exp) exps []) in
                                             tbl @ seq_tbl
      | If' (test,dit,dif)                -> let test_tbl = getting_free_vars test []      in
                                             let dit_tbl  = getting_free_vars dit test_tbl  in
                                             let dif_tbl  = getting_free_vars dif dit_tbl   in
                                             tbl @ dif_tbl
      | Def' (var,exp)                    -> getting_free_vars var tbl  @ getting_free_vars exp tbl
      | Or' (exps)                        -> let or_tbl  = List.rev (List.fold_right (fun exp -> getting_free_vars exp) exps []) in
                                             tbl @ or_tbl
      | Applic' (op, rands)               -> let op_tbl = getting_free_vars op []  in
                                             let applic_tbl =  List.rev (List.fold_right (fun exp -> getting_free_vars exp) rands []) in
                                             tbl @ op_tbl @ applic_tbl
      | ApplicTP' (op, rands)             -> let op_tbl = getting_free_vars op []  in 
                                             let applic_tbl = List.rev (List.fold_right (fun exp -> getting_free_vars exp) rands []) in 
                                             tbl @ op_tbl @ applic_tbl
      | Var'(VarFree x)                   -> tbl@[x]
      | Var'(var)                         -> tbl
      | Set' (var,exp)                    -> getting_free_vars var tbl  @ getting_free_vars exp tbl
      | LambdaSimple'(vars, body)         -> getting_free_vars body tbl
      | LambdaOpt'(vars,opt_vals, body)   -> getting_free_vars body tbl

  let rec make_tupple_fvar index tbl= 
    match tbl with 
      | []       -> []
      | hd::tail -> (hd,(index,"MAKE_UNDEF")) :: make_tupple_fvar (index + 1) tail    


  let make_consts_tbl asts =
    let tbl_default = [Void; Sexpr(Nil);Sexpr(Bool false);Sexpr(Bool true)] in
    let tbl_const = List.flatten (List.map (fun ast -> collect_the_sexprs ast []) asts) in 
    let tbl_const = tbl_default @ tbl_const in 
    let tbl_set =  removing_duplicates tbl_const in
    let tbl_sub_constants = serch_for_all_sub_constants tbl_set in
    let tbl_set_sub_constants = removing_duplicates tbl_sub_constants in
    let tbl_constants = populate_constants_table tbl_set_sub_constants tbl_set_sub_constants  in
    let tbl_constants = make_final_tupple tbl_constants tbl_constants in
    tbl_constants;;  

  let reserved_free_var = ["boolean?"; "float?"; "integer?"; "pair?";
   "null?"; "char?"; "vector?"; "string?";
   "procedure?"; "symbol?"; "string-length";
   "string-ref"; "string-set!"; "make-string";
   "vector-length"; "vector-ref"; "vector-set!";
   "make-vector"; "symbol->string"; 
   "char->integer"; "integer->char"; "eq?";
   "+"; "*"; "-"; "/"; "<"; "="; "car";"cdr"; "cons";"set-car!";"set-cdr!";"apply"];;


  let make_fvars_tbl asts = 
    let tbl_fvar = List.flatten (List.map (fun ast -> getting_free_vars ast []) asts) in
    let union_reserved_fvars = reserved_free_var @ tbl_fvar in
    let tbl_set_fvars = removing_duplicates union_reserved_fvars in 
    let tbl_tupple = make_tupple_fvar 0 tbl_set_fvars in   
    tbl_tupple

 
  let label_in_fvar_table name fvars_tbl = (try 
                                            let (index,_) = (List.assoc name fvars_tbl) in
                                           Printf.sprintf ("fvar_tbl+%d*WORD_SIZE") index 
                                            with any ->  ";debug")

let rec generate consts_tbl fvars_tbl e = generate_helper consts_tbl fvars_tbl e 0 
and generate_helper consts_tbl fvars_tbl e depth = 
  match e with
      | Const'(exp)        ->  

        let (offset,_) = List.assoc exp consts_tbl in
             (Printf.sprintf (
        "\tmov rax, const_tbl+%d\n") offset)^

        ";Const Computition end\n"

      | Seq'(exps)         ->  

       ";Seq Computition start\n"^

        String.concat "\n" (
          List.map 
            (fun exp -> 
              (generate_helper consts_tbl fvars_tbl exp depth)) 
            exps)  ^

       ";Seq Computition end\n"

      | If'(test,dit,dif)  -> 

        let lelse_label =  label_maker "Lelse" in
        let lexit_label =  label_maker "Lexit" in

        (generate_helper consts_tbl fvars_tbl test depth) ^
        "\tcmp rax, SOB_FALSE_ADDRESS\n" ^
        "\tje " ^lelse_label^ "\n" ^
        (generate_helper consts_tbl fvars_tbl dit depth) ^
        "\tjmp " ^lexit_label^ 

       "\n"^
       lelse_label^ ":\n"^
        (generate_helper consts_tbl fvars_tbl dif depth) ^

       lexit_label^ ":\n" ^

      ";If Computition end\n"

      | Or' (exps)         ->  

        let lexit_label =  label_maker "Lexit" in

        ";Or Computition start\n"^

          String.concat "\n" (
            List.map 
              (fun exp -> 
                (generate_helper consts_tbl fvars_tbl exp depth) ^ 
                "\tcmp rax, SOB_FALSE_ADDRESS \n" ^
                "\tjne " ^lexit_label^ "\n") 
            exps) ^
        lexit_label^":\n" ^

        ";Or Computition end\n"

      | Var'(VarParam(_, minor)) ->  

          ";VarParam Computition start\n" ^

                    (Printf.sprintf 
         ("\tmov rax, qword [rbp + 8 * (4 + %d)]\n")  minor)^

          ";VarParam Computition end\n" 

      | Var'(VarBound(_, major, minor)) -> 

        ";VarBound Computition start\n" ^

        "\tmov rax, qword [rbp + 8 * 2]\n" ^
            (Printf.sprintf (
        "\tmov rax, qword [rax + 8 * %d]\n") major) ^
            (Printf.sprintf (
        "\tmov rax, qword [rax + 8 * %d]\n") minor)^

        ";VarBound Computition end\n" 

      | Var'(VarFree(v)) ->  

        ";VarFree Computition start\n" ^

        "\tmov rax, qword ["^ (label_in_fvar_table v fvars_tbl) ^ "]" ^ (Printf.sprintf(";the var is %s\n") v )^

        ";VarFree Computition end\n" 

      | Set'(Var'(VarParam(_, minor)),exp) ->

        (generate_helper consts_tbl fvars_tbl exp depth) ^
        (Printf.sprintf ("\tmov qword [rbp + 8 * (4+%d)], rax\n") minor) ^
          "\tmov rax, SOB_VOID_ADDRESS\n"^

         ";Set VarParam Computition end\n"

      | Set'(Var'(VarBound(_,major,minor)) , exp) ->  

        ";Set VarBound Computition start\n" ^

         (generate_helper consts_tbl fvars_tbl exp depth) ^ 
          "\tmov rbx, qword [rbp + 8 * 2]\n" ^ 
          (Printf.sprintf ("\tmov rbx, qword [rbx + 8 * %d]\n") major) ^
          (Printf.sprintf ("\tmov qword [rbx + 8 * %d], rax\n") minor) ^
          "\tmov rax, SOB_VOID_ADDRESS\n"^

        ";Set VarBound Computition end\n"

      | Set'(Var'(VarFree(v)), exp) -> 

        ";Set VarFree Computition start\n" ^

        (generate_helper consts_tbl fvars_tbl exp depth) ^
         "\tmov qword [" ^ (label_in_fvar_table v fvars_tbl) ^ "], rax\n" ^ 
         "\tmov rax,SOB_VOID_ADDRESS\n"^

         ";Set VarFree Computition end\n" 

      | Def' (Var'(VarFree(v)), exp) -> 

       ";Def Computition start\n" ^

        (generate_helper consts_tbl fvars_tbl exp depth) ^
        "\tmov qword [" ^ label_in_fvar_table v fvars_tbl ^ "], rax\n" ^ 
        "\tmov rax,SOB_VOID_ADDRESS\n"^

       ";Def Computition end\n" 

      | BoxGet'(var) ->

        ";BoxGet Computition start\n" ^ 

        (generate_helper consts_tbl fvars_tbl (Var'(var)) depth) ^
          "\tmov rax, qword [rax]\n" ^
        
        ";BoxGet Computition end\n" 

      | BoxSet'(var,exp) ->  

        ";BoxSet Computition start\n" ^ 

        (generate_helper consts_tbl fvars_tbl exp depth) ^
        "\tpush rax\n" ^
        (generate_helper consts_tbl fvars_tbl (Var'(var)) depth) ^
        "\tpop qword [rax]\n" ^
        "\tmov rax,SOB_VOID_ADDRESS\n"^

        ";BoxSet Computition end\n" 

        | Box'(var) ->  
          (generate_helper consts_tbl fvars_tbl (Var'(var)) depth) ^
          "\tMALLOC rbx, 8\n" ^
          "\tmov [rbx], rax\n" ^
          "\tmov rax, rbx\n" ^
          ";Box Computition end\n" 

      | LambdaSimple'(params,body) -> 

       let depth = depth +1 in
       let lstart_label1     =  label_maker "Ls_start1_" in
       let lfinish_label1    =  label_maker "Ls_finish1_" in

       let lstart_label2     =  label_maker "Ls_start2_" in
       let lfinish_label2    =  label_maker "Ls_finish2_" in
       let lbody_label       =  label_maker "Ls_body" in
       let lend_label        =  label_maker "Ls_end" in

       ";LambdaSimple Computition start\n"^
         "\tpush rcx\n"^
         "\tpush rdx\n"^
         "\tpush r8\n"^ 
         (*                                   Environment Extention                                       *)
         (*                                (store extended env in rbx)                                    *)

         (*                                  Old Environment Copy                                        *)
                                              (Printf.sprintf 
        ("\tmov rax, %d\n") depth)^
         "\tshl rax, 3\n"^
         "\tMALLOC rbx, rax                  ;*rbx*        <- new environment\n"^
                                              (Printf.sprintf 
        ("\tmov rcx, %d                       ;rcx          <- size of the old environment\n") (depth-1))^
                                              (Printf.sprintf
        ("\tmov rdx, %d                       ;rdx          <- size of the new environment\n") depth)^

       "\n"^
          (*                                   ribs  -workk                                     *)
       lstart_label1^":\n"^   
         "\tcmp rcx, 0\n"^
         "\tje "^lfinish_label1^"\n"^ 
         "\tdec rcx\n"^ 
         "\tdec rdx\n"^     
         "\tmov rax, qword [rbp + 8 * 2]      ;rax          <- oldEnv\n"^ 
         "\tmov rax, qword [rax + 8 * rcx]    ;rax          <- oldEnv [rcx]\n"^ 
         "\tmov qword [rbx + 8 * rdx], rax    ;newEnv [rdx] <- rax\n"^ 

         "\tjmp "^lstart_label1^"\n"^ 
       "\n"^
       lfinish_label1^":\n"^ 

        (*                                    Parametes Copy                                            *)
         "\tmov rcx, qword [rbp+8*3]                        ;rcx          <- n (args count)\n"^ 
         "\tshl rcx, 3\n"^ 
         "\tadd rcx,8                                       ;rcx          <- add place for Magic\n"^ 
         "\tMALLOC rdx, rcx                                 ;*rdx*        <- newRib\n"^
         "\tshr rcx, 3                                      ;rcx <- n \n" ^
         "\t;mov qword [rdx+rcx*WORD_SIZE], SOB_NIL_ADDRESS  ;\n"^

         "\n"^
       lstart_label2^":\n"^ 
         "\tcmp rcx, 0\n"^
         "\tje "^lfinish_label2^"\n"^
         "\t;jl "^lfinish_label2^"\n" (*TODO:*)^

         "\tlea rax,  [rbp+4*WORD_SIZE]            ;rax          <- &(args[0])\n"^ 
         "\tdec rcx\n"^ 
         "\tmov rax,  qword[rax+rcx*WORD_SIZE]     ;rax          <- args[rcx]\n"^ 
         "\tlea r8,   [rdx+rcx*WORD_SIZE]          ;r8           <- &(newRib[rcx])\n"^ 
         "\tmov qword [r8], rax                    ;newRib[rcx]  <- args[rcx]\n"^
 
         "\tjmp "^lstart_label2^"\n"^ 

         "\n"^
       lfinish_label2^":\n"^ 
         "\tmov qword [rbx], rdx               ;newEnv[0]  <- &(newRib)\n"^

       (*                                     Closure Creation                                           *)
       (*                                 (during compilation time)                                      *)
        "\tMAKE_CLOSURE (rax, rbx,"^lbody_label^")\n"^
        "\tjmp "^lend_label^"\n"^
       (*                                    Closure Computition                                         *)
       (*                                     (during run time)                                          *)
       "\n"^
       lbody_label^":\n"^
        "\tpush rbp\n"^
        "\tmov rbp, rsp\n"^

                       (* (Printf.sprintf  *)
         (* "\tmov rax, %d                        ;rax        <- List.length <vars>\n" (List.length params))^ *)
         (* "\tcmp rax, PARAM_COUNT\n"^  *)
         (* "\tjne "^lerror_label^"\n"^  *)

      (generate_helper consts_tbl fvars_tbl body depth)^ "\n"^

        "\tpop rbp\n"^
        "\tret\n"^
      lend_label^":\n"^

        (* "\tmov rsp, rbp\n"^ *)
       "\tpop r8\n"^
        "\tpop rdx\n"^
        "\tpop rcx\n"^ 

      ";LambdaSimple Computition end\n" 

      | Applic' (op, rands)        ->

         let after_error =  label_maker "Lexit" in
         let error =  label_maker "Lfail" in

         "\tpush r8\n"^
         "\tpush qword SOB_NIL_ADDRESS\n" ^

         (String.concat "\n" 
           (List.rev_map 
            (fun rand -> 
              (generate_helper consts_tbl fvars_tbl rand depth)^
              "\tpush rax\n"
            ) 
            rands))^
                        (Printf.sprintf 
         "\tpush %d                                    ;push number of args\n" (List.length rands))^

        (generate_helper consts_tbl fvars_tbl op depth) ^

         "\tcmp byte [rax],T_CLOSURE                  ;verify that rax has type closure\n"^
         (Printf.sprintf ("jne %s\n") error) ^
         "\tmov r8, qword[rax + TYPE_SIZE]           ;r8 <- env\n"^
         "\tpush r8                                   ;push closure.env\n"^
         "\tCLOSURE_CODE rax, rax\n" ^
         "\tcall rax                                  ;call closure.code\n"^
         "\tadd rsp, 8*1                              ;pop env\n"^
         "\tpop rbx                                   ;pop arg count\n"^
         "\tshl rbx, 3                                ;rbx = rbx * 8\n"^
         "\tadd rsp, rbx                              ;pop args\n"^
         "\tadd rsp, 8                                ;going magic\n"^
         "\tpop r8\n"^
          (Printf.sprintf ("jmp %s\n") after_error) ^
          (Printf.sprintf ("%s:\n") error) ^
          "call exit\n"^
          (Printf.sprintf("%s:\n\n") after_error) ^
      ";Applic Computition end\n"

      | ApplicTP' (op, rands)             ->
 
           let failLabel =  label_maker "Lfail" in

            let  size_of_frame = 5 + (List.length rands) in

            "push qword SOB_NIL_ADDRESS\n ; TODO: magic support \n" ^
     
             (String.concat "\n" 
               (List.map 
                (fun rand -> 
                  (generate_helper consts_tbl fvars_tbl rand depth)^
                  "\tpush rax\n"
                ) 
                (List.rev rands)))^
            (Printf.sprintf "\tpush %d    ;push number of args\n" (List.length rands))^
     
            (generate_helper consts_tbl fvars_tbl op depth) ^
     
             "\tcmp byte[rax],T_CLOSURE            ;verify type closure\n"^
              (Printf.sprintf ("jne %s\n") failLabel) ^
             "\tCLOSURE_ENV r8, rax                       ;r8 <- env\n"^
             "\tpush r8                                   ;push closure.env\n"^
             "\tpush qword [rbp + 8 * 1]                  ; old ret addr \n " ^
             "\tmov r10, qword[rbp]                       ; old rbp \n " ^
             ";fix the stack\n" ^
               (Printf.sprintf("\tSHIFT_FRAME %d \n ") size_of_frame) ^  
                (* Printf.sprintf("\tDYN_SHIFT_FRAME %d \n ") size_of_frame  ^    *)
             ";end fix the stack\n" ^
             "CLOSURE_CODE rax,rax\n" ^
             "\tmov rbp, r10\n" ^ 
             "\tjmp rax\n" ^
             (Printf.sprintf ("%s:\n") failLabel) ^
             "call exit\n" 
          
      | LambdaOpt'(vars,opt_vals, body)   ->

  let depth = depth +1 in
       let lstart_label1     =  label_maker "Lo_start1_" in
       let lfinish_label1    =  label_maker "Lo_finish1_" in

       let lstart_label2     =  label_maker "Lo_start2_" in
       let lfinish_label2    =  label_maker "Lo_finish2_" in
       let lbody_label       =  label_maker "Lo_body" in
       let lend_label        =  label_maker "Lo_end" in

       ";LambdaSimple Computition start\n"^
         "\tpush rcx\n"^
         "\tpush rdx\n"^
         "\tpush r8\n"^ 
         (*                                   Environment Extention                                       *)
         (*                                (store extended env in rbx)                                    *)

         (*                                  Old Environment Copy                                        *)
                                              (Printf.sprintf 
        ("\tmov rax, %d\n") depth)^
         "\tshl rax, 3\n"^
         "\tMALLOC rbx, rax                  ;*rbx*        <- new environment\n"^
                                              (Printf.sprintf 
        ("\tmov rcx, %d                       ;rcx          <- size of the old environment\n") (depth-1))^
                                              (Printf.sprintf
        ("\tmov rdx, %d                       ;rdx          <- size of the new environment\n") depth)^

       "\n"^
          (*                                   ribs  -workk                                     *)
       lstart_label1^":\n"^   
         "\tcmp rcx, 0\n"^
         "\tje "^lfinish_label1^"\n"^ 
         "\tdec rcx\n"^ 
         "\tdec rdx\n"^     
         "\tmov rax, qword [rbp + 8 * 2]      ;rax          <- oldEnv\n"^ 
         "\tmov rax, qword [rax + 8 * rcx]    ;rax          <- oldEnv [rcx]\n"^ 
         "\tmov qword [rbx + 8 * rdx], rax    ;newEnv [rdx] <- rax\n"^ 

         "\tjmp "^lstart_label1^"\n"^ 
       "\n"^
       lfinish_label1^":\n"^ 

        (*                                    Parametes Copy                                            *)
         "\tmov rcx, qword [rbp+8*3]                        ;rcx          <- n (args count)\n"^ 
         "\tshl rcx, 3\n"^ 
         "\tadd rcx,8                                       ;rcx          <- add place for Magic\n"^ 
         "\tMALLOC rdx, rcx                                 ;*rdx*        <- newRib\n"^
         "\tshr rcx, 3                                      ;rcx <- n \n" ^
         "\t;mov qword [rdx+rcx*WORD_SIZE], SOB_NIL_ADDRESS  ;\n"^

         "\n"^
       lstart_label2^":\n"^ 
         "\tcmp rcx, 0\n"^
         "\tje "^lfinish_label2^"\n"^
         "\t;jl "^lfinish_label2^"\n" (*TODO:*)^

         "\tlea rax,  [rbp+4*WORD_SIZE]            ;rax          <- &(args[0])\n"^ 
         "\tdec rcx\n"^ 
         "\tmov rax,  qword[rax+rcx*WORD_SIZE]     ;rax          <- args[rcx]\n"^ 
         "\tlea r8,   [rdx+rcx*WORD_SIZE]          ;r8           <- &(newRib[rcx])\n"^ 
         "\tmov qword [r8], rax                    ;newRib[rcx]  <- args[rcx]\n"^
 
         "\tjmp "^lstart_label2^"\n"^ 

         "\n"^
       lfinish_label2^":\n"^ 
         "\tmov qword [rbx], rdx               ;newEnv[0]  <- &(newRib)\n"^

       (*                                     Closure Creation                                           *)
       (*                                 (during compilation time)                                      *)
        "\tMAKE_CLOSURE (rax, rbx,"^lbody_label^")\n"^
        "\tjmp "^lend_label^"\n"^
       (*                                    Closure Computition                                         *)
       (*                                     (during run time)                                          *)
       "\n"^
       lbody_label^":\n"^
        "\tpush rbp\n"^
        "\tmov rbp, rsp\n"^
        (Printf.sprintf ("\tADJUST_THE_STACK %d \n") ((List.length vars)+1))^

      (generate_helper consts_tbl fvars_tbl body depth)^ "\n"^

        "\tpop rbp\n"^
        "\tret\n"^

      "\n"^
      lend_label^":\n"^

        (* "\tmov rsp, rbp\n"^ *)
       "\tpop r8\n"^
        "\tpop rdx\n"^
        "\tpop rcx\n"^ 

      ";LambdaOpt Computition end\n" 

      | _   ->  "debug\n";;
  
    
     
end;;