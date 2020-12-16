#use "code-gen.ml";;
  

(*   func for debug!!!!!!!!!!!!!!!!!!!!! *)
(* let () = Printexc.record_backtrace true;; *)

  let file_to_string f =
    let ic = open_in f in
    let s = really_input_string ic (in_channel_length ic) in
    close_in ic;
    s;;

  let string_to_asts s = List.map Semantics.run_semantics
                          (Tag_Parser.tag_parse_expressions
                              (Reader.read_sexprs s));;

  let primitive_names_to_labels = 
    ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
    "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
    "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
    "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
    "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
    "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
    "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
    "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ"; "car","car";
    "cdr","cdr"; "cons","cons"; "set-car!", "setcar";"set-cdr!", "setcdr";"apply", "apply"];;


  (*debug functions*)
(*      let test_free_var = 
    let asts = string_to_asts "" in
    let fvars_tbl = Code_Gen.make_fvars_tbl asts in
    fvars_tbl;;  *)
(* 
    let test_ast = 
    let asts = string_to_asts " 
                          (define andmap (lambda (p lst)
                      (or (null? lst)
                          (and (p (car lst)) (andmap p (cdr lst)))) ))
              ; make-matrix creates a matrix (a vector of vectors).
              ; make-matrix creates a matrix (a vector of vectors).
              (define make-matrix
                (lambda (rows columns)
                (letrec ([loop (lambda (m i)
                (if (= i rows)
                    (begin m)
                    (begin
                      (vector-set! m i (make-vector columns))
                      (loop m (+ i 1)))))])
              (loop (make-vector rows) 0)))) 

              ; matrix? checks to see if its argument is a matrix.
              ; It isn't foolproof, but it's generally good enough.
              (define matrix?
                (lambda (x)
                  (and (vector? x)
                      (> (vector-length x) 0)
                      (vector? (vector-ref x 0)))))

              ; matrix-rows returns the number of rows in a matrix.
              (define matrix-rows
                (lambda (x)
                  (vector-length x)))

              ; matrix-columns returns the number of columns in a matrix.
              (define matrix-columns
                (lambda (x)
                  (vector-length (vector-ref x 0))))

              ; matrix-ref returns the jth element of the ith row.
              (define matrix-ref
                (lambda (m i j)
                  (vector-ref (vector-ref m i) j)))

              ; matrix-set! changes the jth element of the ith row.
              (define matrix-set!
                (lambda (m i j x)
                  (vector-set! (vector-ref m i) j x)))

              ; mat-sca-mul multiplies a matrix by a scalar.
              (define mat-sca-mul
                (lambda (x m)
                  (let* ([nr (matrix-rows m)]
                        [nc (matrix-columns m)]
                        [r (make-matrix nr nc)])
                        (letrec ([loop (lambda (i)
                        (if (= i nr)
                            (begin r)
                            (begin
                                (letrec ([loop2 (lambda (j)
                                (if (= j nc)
                                    #t
                                    (begin
                                      (matrix-set! r i j (* x (matrix-ref m i j)))
                                      (loop2 (+ j 1)))))])
                (loop2 0))
                              (loop (+ i 1)))))])
              (loop 0)))))

              ; mat-mat-mul multiplies one matrix by another, after verifying
              ; that the first matrix has as many columns as the second
              ; matrix has rows.
              (define mat-mat-mul
                (lambda (m1 m2)
                  (let* ([nr1 (matrix-rows m1)]
                        [nr2 (matrix-rows m2)]
                        [nc2 (matrix-columns m2)]
                        [r (make-matrix nr1 nc2)])
                        (letrec ([loop (lambda (i)
                        (if (= i nr1)
                            (begin r)
                            (begin
                                (letrec ([loop (lambda (j)
                                (if (= j nc2)
                                    #t
                                    (begin
                                        (letrec ([loop (lambda (k a)
                                        (if (= k nr2)
                                            (begin (matrix-set! r i j a))
                                            (begin
                                              (loop
                                                (+ k 1)
                                                (+ a
                                                  (* (matrix-ref m1 i k)
                                                      (matrix-ref m2 k j)))))))])
                                            (loop 0 0))
                                      (loop (+ j 1)))))])
                                (loop 0))
                        (loop (+ i 1)))))])
              (loop 0))))) 


                ; mul is the generic matrix/scalar multiplication procedure
                (define mul
                  (lambda (x y)
                    (cond
                      [(number? x)
                      (cond
                        [(number? y) (* x y)]
                        [(matrix? y) (mat-sca-mul x y)]
                        [else \"this should be an error, but you don't support exceptions\"])]
                      [(matrix? x)
                      (cond
                        [(number? y) (mat-sca-mul y x)]
                        [(matrix? y) (mat-mat-mul x y)]
                        [else \"this should be an error, but you don't support exceptions\"])]
                      [else \"this should be an error, but you don't support exceptions\"])))


                (mul '#(#(2 3 4)
                #(3 4 5))
              '#(#(1) #(2) #(3)))

              (mul '#(#(1 2 3))
                  '#(#(2 3)
                      #(3 4)
                      #(4 5)))

              (mul '#(#(1 2 3)
                      #(4 5 6))
                  '#(#(1 2 3 4)
                      #(2 3 4 5)
                      #(3 4 5 6)))


              (mul -2
                '#(#(3 -2 -1)
                  #(-3 0 -5)
                  #(7 -1 -1))
                  )


                  (mul 0.5 '#(#(1 2 3)) )
                  (mul 1 0.5)
    " in
    let fvars_tbl = Code_Gen.make_consts_tbl asts in
    fvars_tbl;;  
  *)

  let make_prologue consts_tbl fvars_tbl =
    let get_const_address const =  (try 
                                     let (offset,_) = List.assoc const consts_tbl in
                                      Printf.sprintf ("const_tbl+%d") offset
                                  with any ->  ";eranisidiot")   in    (*TODO: delete *)

    let get_fvar_address const = ( try
                                      let (index,_) = List.assoc const fvars_tbl in 
                                      Printf.sprintf ("fvar_tbl+%d *WORD_SIZE") index
                                  with any ->  ";eranisidiot")   in    (*TODO: delete *)
                              
    let make_primitive_closure (prim, label) =

                        "    MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ label  ^ ")
                              mov [" ^ (get_fvar_address prim)  ^ "], rax" in

    let make_constant (c, (a, s)) = s in
    
  "
  ;;; All the macros and the scheme-object printing procedure
  ;;; are defined in compiler.s
  %include \"compiler.s\"

  section .bss
  malloc_pointer:
      resq 1

  section .data
  const_tbl:
  " ^ (String.concat "\n" (List.map make_constant consts_tbl)) ^ "

  ;;; These macro definitions are required for the primitive
  ;;; definitions in the epilogue to work properly
  %define SOB_VOID_ADDRESS " ^ get_const_address Void ^ "
  %define SOB_NIL_ADDRESS " ^ get_const_address (Sexpr Nil) ^ "
  %define SOB_FALSE_ADDRESS " ^ get_const_address (Sexpr (Bool false)) ^ "
  %define SOB_TRUE_ADDRESS " ^ get_const_address (Sexpr (Bool true)) ^ "

  fvar_tbl:
  " ^ (String.concat "\n" (List.map (fun _ -> "dq T_UNDEFINED") fvars_tbl)) ^ "

  section .text
  global main
  main:
      ;; set up the heap
      mov rdi, GB(4)
      call malloc
      mov [malloc_pointer], rax

      ;; Set up the dummy activation frame
      ;; The dummy return address is T_UNDEFINED
      ;; (which a is a macro for 0) so that returning
      ;; from the top level (which SHOULD NOT HAPPEN
      ;; AND IS A BUG) will cause a segfault.
      push rbp
      push qword SOB_NIL_ADDRESS ; magic
      push 0
      push qword SOB_NIL_ADDRESS  ; dummy env
      push qword T_UNDEFINED
      push rsp
      mov rbp, rsp

      call code_fragment
      add rsp, 4*8
      pop rbp
      ret

  code_fragment:
      ;; Set up the primitive stdlib fvars:
      ;; Since the primtive procedures are defined in assembly,
      ;; they are not generated by scheme (define ...) expressions.
      ;; This is where we emulate the missing (define ...) expressions
      ;; for all the primitive procedures.
  " ^   (String.concat "\n" (List.map make_primitive_closure primitive_names_to_labels)) ^  
  "
  ";;

  let epilogue = ";epilogue not needed, not implemented";;

  exception X_missing_input_file;;

  try
    let infile = Sys.argv.(1) in
    let code = 
             (file_to_string "stdlib.scm") ^    
            (file_to_string infile) in 

    let asts = string_to_asts code in
    let consts_tbl = Code_Gen.make_consts_tbl asts in
    let fvars_tbl = Code_Gen.make_fvars_tbl asts in
    let generate = Code_Gen.generate consts_tbl fvars_tbl in
    let code_fragment = 
    ";**********************************************************************************\n"^
    String.concat "\n\n"
                          (List.map
                            (fun ast -> (generate ast) ^ "\n    call write_sob_if_not_void")
                            asts) ^
  "\n;**********************************************************************************\n"
                        in
    let provided_primitives = file_to_string "prims.s" in
                    
    print_string ((make_prologue consts_tbl fvars_tbl)  ^
                    code_fragment ^ "\n ret \n " ^
                      provided_primitives ^ "\n" ^ epilogue)

  with Invalid_argument(x) -> raise X_missing_input_file;;
