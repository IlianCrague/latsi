
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | VAVERS
    | VAR of (
# 12 "src/parser.mly"
       (char)
# 16 "src/parser.ml"
  )
    | STRING of (
# 11 "src/parser.mly"
      (string)
# 21 "src/parser.ml"
  )
    | SI
    | REM
    | PLUS
    | PG
    | PD
    | NL
    | NEQ
    | MULT
    | MOINS
    | LTE
    | LT
    | INT of (
# 13 "src/parser.mly"
       (int)
# 37 "src/parser.ml"
  )
    | IMPRIME
    | GTE
    | GT
    | FIN
    | EQ
    | EOF
    | ENTREE
    | DIV
    | CR
    | COMMA
    | ALORS
  
end

include MenhirBasics

# 1 "src/parser.mly"
  
open Ast

# 59 "src/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_input) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: input. *)

  | MenhirState05 : (('s, _menhir_box_input) _menhir_cell1_nombre, _menhir_box_input) _menhir_state
    (** State 05.
        Stack shape : nombre.
        Start symbol: input. *)

  | MenhirState06 : (('s, _menhir_box_input) _menhir_cell1_VAVERS, _menhir_box_input) _menhir_state
    (** State 06.
        Stack shape : VAVERS.
        Start symbol: input. *)

  | MenhirState08 : (('s, _menhir_box_input) _menhir_cell1_PLUS, _menhir_box_input) _menhir_state
    (** State 08.
        Stack shape : PLUS.
        Start symbol: input. *)

  | MenhirState09 : (('s, _menhir_box_input) _menhir_cell1_PG, _menhir_box_input) _menhir_state
    (** State 09.
        Stack shape : PG.
        Start symbol: input. *)

  | MenhirState10 : (('s, _menhir_box_input) _menhir_cell1_MOINS, _menhir_box_input) _menhir_state
    (** State 10.
        Stack shape : MOINS.
        Start symbol: input. *)

  | MenhirState11 : ((('s, _menhir_box_input) _menhir_cell1_MOINS, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_state
    (** State 11.
        Stack shape : MOINS terme.
        Start symbol: input. *)

  | MenhirState12 : ((('s, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_cell1_PLUS, _menhir_box_input) _menhir_state
    (** State 12.
        Stack shape : terme PLUS.
        Start symbol: input. *)

  | MenhirState13 : (((('s, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_cell1_PLUS, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_state
    (** State 13.
        Stack shape : terme PLUS terme.
        Start symbol: input. *)

  | MenhirState14 : ((('s, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_cell1_MOINS, _menhir_box_input) _menhir_state
    (** State 14.
        Stack shape : terme MOINS.
        Start symbol: input. *)

  | MenhirState15 : (((('s, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_cell1_MOINS, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_state
    (** State 15.
        Stack shape : terme MOINS terme.
        Start symbol: input. *)

  | MenhirState20 : (('s, _menhir_box_input) _menhir_cell1_facteur, _menhir_box_input) _menhir_state
    (** State 20.
        Stack shape : facteur.
        Start symbol: input. *)

  | MenhirState21 : (('s, _menhir_box_input) _menhir_cell1_MULT, _menhir_box_input) _menhir_state
    (** State 21.
        Stack shape : MULT.
        Start symbol: input. *)

  | MenhirState23 : (('s, _menhir_box_input) _menhir_cell1_DIV, _menhir_box_input) _menhir_state
    (** State 23.
        Stack shape : DIV.
        Start symbol: input. *)

  | MenhirState25 : (('s, _menhir_box_input) _menhir_cell1_op_facteur_list, _menhir_box_input) _menhir_state
    (** State 25.
        Stack shape : op_facteur_list.
        Start symbol: input. *)

  | MenhirState30 : (('s, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_state
    (** State 30.
        Stack shape : terme.
        Start symbol: input. *)

  | MenhirState34 : ((('s, _menhir_box_input) _menhir_cell1_PLUS, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_state
    (** State 34.
        Stack shape : PLUS terme.
        Start symbol: input. *)

  | MenhirState38 : (('s, _menhir_box_input) _menhir_cell1_VAR, _menhir_box_input) _menhir_state
    (** State 38.
        Stack shape : VAR.
        Start symbol: input. *)

  | MenhirState40 : (('s, _menhir_box_input) _menhir_cell1_SI, _menhir_box_input) _menhir_state
    (** State 40.
        Stack shape : SI.
        Start symbol: input. *)

  | MenhirState48 : ((('s, _menhir_box_input) _menhir_cell1_SI, _menhir_box_input) _menhir_cell1_expression _menhir_cell0_relop, _menhir_box_input) _menhir_state
    (** State 48.
        Stack shape : SI expression relop.
        Start symbol: input. *)

  | MenhirState50 : (((('s, _menhir_box_input) _menhir_cell1_SI, _menhir_box_input) _menhir_cell1_expression _menhir_cell0_relop, _menhir_box_input) _menhir_cell1_expression, _menhir_box_input) _menhir_state
    (** State 50.
        Stack shape : SI expression relop expression.
        Start symbol: input. *)

  | MenhirState54 : (('s, _menhir_box_input) _menhir_cell1_IMPRIME, _menhir_box_input) _menhir_state
    (** State 54.
        Stack shape : IMPRIME.
        Start symbol: input. *)

  | MenhirState59 : (('s, _menhir_box_input) _menhir_cell1_expr_or_string, _menhir_box_input) _menhir_state
    (** State 59.
        Stack shape : expr_or_string.
        Start symbol: input. *)

  | MenhirState63 : (('s, _menhir_box_input) _menhir_cell1_ENTREE, _menhir_box_input) _menhir_state
    (** State 63.
        Stack shape : ENTREE.
        Start symbol: input. *)

  | MenhirState67 : (('s, _menhir_box_input) _menhir_cell1_var, _menhir_box_input) _menhir_state
    (** State 67.
        Stack shape : var.
        Start symbol: input. *)

  | MenhirState72 : ((('s, _menhir_box_input) _menhir_cell1_nombre, _menhir_box_input) _menhir_cell1_instruction, _menhir_box_input) _menhir_state
    (** State 72.
        Stack shape : nombre instruction.
        Start symbol: input. *)


and ('s, 'r) _menhir_cell1_expr_or_string = 
  | MenhirCell1_expr_or_string of 's * ('s, 'r) _menhir_state * (Ast.string_or_exp)

and ('s, 'r) _menhir_cell1_expression = 
  | MenhirCell1_expression of 's * ('s, 'r) _menhir_state * (Ast.expression)

and ('s, 'r) _menhir_cell1_facteur = 
  | MenhirCell1_facteur of 's * ('s, 'r) _menhir_state * (Ast.facteur)

and ('s, 'r) _menhir_cell1_instruction = 
  | MenhirCell1_instruction of 's * ('s, 'r) _menhir_state * (Ast.instruction)

and ('s, 'r) _menhir_cell1_nombre = 
  | MenhirCell1_nombre of 's * ('s, 'r) _menhir_state * (Ast.nombre)

and ('s, 'r) _menhir_cell1_op_facteur_list = 
  | MenhirCell1_op_facteur_list of 's * ('s, 'r) _menhir_state * (Ast.op_facteur * Ast.facteur)

and 's _menhir_cell0_relop = 
  | MenhirCell0_relop of 's * (Ast.relop)

and ('s, 'r) _menhir_cell1_terme = 
  | MenhirCell1_terme of 's * ('s, 'r) _menhir_state * (Ast.terme)

and ('s, 'r) _menhir_cell1_var = 
  | MenhirCell1_var of 's * ('s, 'r) _menhir_state * (Ast.var)

and ('s, 'r) _menhir_cell1_DIV = 
  | MenhirCell1_DIV of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ENTREE = 
  | MenhirCell1_ENTREE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_IMPRIME = 
  | MenhirCell1_IMPRIME of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MOINS = 
  | MenhirCell1_MOINS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MULT = 
  | MenhirCell1_MULT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PG = 
  | MenhirCell1_PG of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PLUS = 
  | MenhirCell1_PLUS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_SI = 
  | MenhirCell1_SI of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_VAR = 
  | MenhirCell1_VAR of 's * ('s, 'r) _menhir_state * (
# 12 "src/parser.mly"
       (char)
# 248 "src/parser.ml"
)

and ('s, 'r) _menhir_cell1_VAVERS = 
  | MenhirCell1_VAVERS of 's * ('s, 'r) _menhir_state

and _menhir_box_input = 
  | MenhirBox_input of (Ast.programme) [@@unboxed]

let _menhir_action_01 =
  fun l ->
    (
# 44 "src/parser.mly"
                                                              ( l )
# 262 "src/parser.ml"
     : (Ast.expr_list))

let _menhir_action_02 =
  fun s ->
    (
# 47 "src/parser.mly"
                     ( String s )
# 270 "src/parser.ml"
     : (Ast.string_or_exp))

let _menhir_action_03 =
  fun e ->
    (
# 48 "src/parser.mly"
                     ( Expression_s_or_e e )
# 278 "src/parser.ml"
     : (Ast.string_or_exp))

let _menhir_action_04 =
  fun t ->
    (
# 54 "src/parser.mly"
          ( (Plus t) :: [] )
# 286 "src/parser.ml"
     : (Ast.expression))

let _menhir_action_05 =
  fun l t ->
    (
# 55 "src/parser.mly"
                                 ( (Plus t) :: l )
# 294 "src/parser.ml"
     : (Ast.expression))

let _menhir_action_06 =
  fun l t ->
    (
# 56 "src/parser.mly"
                                      ( (Plus t) :: l )
# 302 "src/parser.ml"
     : (Ast.expression))

let _menhir_action_07 =
  fun l t ->
    (
# 57 "src/parser.mly"
                                       ( (Moins t) :: l )
# 310 "src/parser.ml"
     : (Ast.expression))

let _menhir_action_08 =
  fun v ->
    (
# 78 "src/parser.mly"
         ( Var_f(Var v) )
# 318 "src/parser.ml"
     : (Ast.facteur))

let _menhir_action_09 =
  fun n ->
    (
# 79 "src/parser.mly"
            ( Nombre_f(n) )
# 326 "src/parser.ml"
     : (Ast.facteur))

let _menhir_action_10 =
  fun e ->
    (
# 80 "src/parser.mly"
                      ( Expression_f(e) )
# 334 "src/parser.ml"
     : (Ast.facteur))

let _menhir_action_11 =
  fun p ->
    (
# 29 "src/parser.mly"
                       ( p )
# 342 "src/parser.ml"
     : (Ast.programme))

let _menhir_action_12 =
  fun s ->
    (
# 34 "src/parser.mly"
                      ( Imprime s)
# 350 "src/parser.ml"
     : (Ast.instruction))

let _menhir_action_13 =
  fun e1 e2 i op ->
    (
# 35 "src/parser.mly"
                                                              ( Si_Alors (e1, op, e2, i) )
# 358 "src/parser.ml"
     : (Ast.instruction))

let _menhir_action_14 =
  fun e ->
    (
# 36 "src/parser.mly"
                      ( Vavers e )
# 366 "src/parser.ml"
     : (Ast.instruction))

let _menhir_action_15 =
  fun vs ->
    (
# 37 "src/parser.mly"
                     ( Entree vs )
# 374 "src/parser.ml"
     : (Ast.instruction))

let _menhir_action_16 =
  fun e v ->
    (
# 38 "src/parser.mly"
                        ( Let (Var v,e) )
# 382 "src/parser.ml"
     : (Ast.instruction))

let _menhir_action_17 =
  fun () ->
    (
# 39 "src/parser.mly"
      ( Fin )
# 390 "src/parser.ml"
     : (Ast.instruction))

let _menhir_action_18 =
  fun s ->
    (
# 40 "src/parser.mly"
               ( Rem s )
# 398 "src/parser.ml"
     : (Ast.instruction))

let _menhir_action_19 =
  fun () ->
    (
# 41 "src/parser.mly"
     ( NL )
# 406 "src/parser.ml"
     : (Ast.instruction))

let _menhir_action_20 =
  fun () ->
    (
# 216 "<standard.mly>"
    ( [] )
# 414 "src/parser.ml"
     : ((Ast.op_facteur * Ast.facteur) list))

let _menhir_action_21 =
  fun x xs ->
    (
# 219 "<standard.mly>"
    ( x :: xs )
# 422 "src/parser.ml"
     : ((Ast.op_facteur * Ast.facteur) list))

let _menhir_action_22 =
  fun n ->
    (
# 18 "src/parser.mly"
              ( Nombre n )
# 430 "src/parser.ml"
     : (Ast.nombre))

let _menhir_action_23 =
  fun f ->
    (
# 74 "src/parser.mly"
                  ( (Mult, f) )
# 438 "src/parser.ml"
     : (Ast.op_facteur * Ast.facteur))

let _menhir_action_24 =
  fun f ->
    (
# 75 "src/parser.mly"
                 ( (Div, f) )
# 446 "src/parser.ml"
     : (Ast.op_facteur * Ast.facteur))

let _menhir_action_25 =
  fun t ->
    (
# 66 "src/parser.mly"
           ( Plus t )
# 454 "src/parser.ml"
     : (Ast.operateur_terme))

let _menhir_action_26 =
  fun t ->
    (
# 67 "src/parser.mly"
                ( Plus t )
# 462 "src/parser.ml"
     : (Ast.operateur_terme))

let _menhir_action_27 =
  fun t ->
    (
# 68 "src/parser.mly"
                 ( Moins t )
# 470 "src/parser.ml"
     : (Ast.operateur_terme))

let _menhir_action_28 =
  fun op ->
    (
# 61 "src/parser.mly"
                       ( [op] )
# 478 "src/parser.ml"
     : (Ast.operateur_terme list))

let _menhir_action_29 =
  fun l t ->
    (
# 62 "src/parser.mly"
                                        ( (Plus t) :: l )
# 486 "src/parser.ml"
     : (Ast.operateur_terme list))

let _menhir_action_30 =
  fun l t ->
    (
# 63 "src/parser.mly"
                                         ( (Moins t) :: l )
# 494 "src/parser.ml"
     : (Ast.operateur_terme list))

let _menhir_action_31 =
  fun l ->
    (
# 31 "src/parser.mly"
                                                                                ( Programme l )
# 502 "src/parser.ml"
     : (Ast.programme))

let _menhir_action_32 =
  fun () ->
    (
# 21 "src/parser.mly"
        ( NEQ )
# 510 "src/parser.ml"
     : (Ast.relop))

let _menhir_action_33 =
  fun () ->
    (
# 22 "src/parser.mly"
        ( LTE )
# 518 "src/parser.ml"
     : (Ast.relop))

let _menhir_action_34 =
  fun () ->
    (
# 23 "src/parser.mly"
       ( LT )
# 526 "src/parser.ml"
     : (Ast.relop))

let _menhir_action_35 =
  fun () ->
    (
# 24 "src/parser.mly"
       ( GT )
# 534 "src/parser.ml"
     : (Ast.relop))

let _menhir_action_36 =
  fun () ->
    (
# 25 "src/parser.mly"
        ( GTE )
# 542 "src/parser.ml"
     : (Ast.relop))

let _menhir_action_37 =
  fun () ->
    (
# 26 "src/parser.mly"
       ( EQ )
# 550 "src/parser.ml"
     : (Ast.relop))

let _menhir_action_38 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 558 "src/parser.ml"
     : (Ast.expr_list))

let _menhir_action_39 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 566 "src/parser.ml"
     : (Ast.expr_list))

let _menhir_action_40 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 574 "src/parser.ml"
     : (Ast.var_list))

let _menhir_action_41 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 582 "src/parser.ml"
     : (Ast.var_list))

let _menhir_action_42 =
  fun i n ->
    let x = 
# 31 "src/parser.mly"
                                                                (Ligne (n, i))
# 590 "src/parser.ml"
     in
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 595 "src/parser.ml"
     : (Ast.ligne list))

let _menhir_action_43 =
  fun i n xs ->
    let x = 
# 31 "src/parser.mly"
                                                                (Ligne (n, i))
# 603 "src/parser.ml"
     in
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 608 "src/parser.ml"
     : (Ast.ligne list))

let _menhir_action_44 =
  fun f fl ->
    (
# 71 "src/parser.mly"
                                 (Terme (f, fl))
# 616 "src/parser.ml"
     : (Ast.terme))

let _menhir_action_45 =
  fun v ->
    (
# 19 "src/parser.mly"
           ( Var v )
# 624 "src/parser.ml"
     : (Ast.var))

let _menhir_action_46 =
  fun l ->
    (
# 50 "src/parser.mly"
                                                  ( l )
# 632 "src/parser.ml"
     : (Ast.var_list))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | ALORS ->
        "ALORS"
    | COMMA ->
        "COMMA"
    | CR ->
        "CR"
    | DIV ->
        "DIV"
    | ENTREE ->
        "ENTREE"
    | EOF ->
        "EOF"
    | EQ ->
        "EQ"
    | FIN ->
        "FIN"
    | GT ->
        "GT"
    | GTE ->
        "GTE"
    | IMPRIME ->
        "IMPRIME"
    | INT _ ->
        "INT"
    | LT ->
        "LT"
    | LTE ->
        "LTE"
    | MOINS ->
        "MOINS"
    | MULT ->
        "MULT"
    | NEQ ->
        "NEQ"
    | NL ->
        "NL"
    | PD ->
        "PD"
    | PG ->
        "PG"
    | PLUS ->
        "PLUS"
    | REM ->
        "REM"
    | SI ->
        "SI"
    | STRING _ ->
        "STRING"
    | VAR _ ->
        "VAR"
    | VAVERS ->
        "VAVERS"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_02 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_input =
    fun _menhir_stack _v ->
      let l = _v in
      let _v = _menhir_action_31 l in
      let p = _v in
      let _v = _menhir_action_11 p in
      MenhirBox_input _v
  
  let rec _menhir_goto_separated_nonempty_list_CR___anonymous_0_ : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState72 ->
          _menhir_run_73 _menhir_stack _v
      | MenhirState00 ->
          _menhir_run_02 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_73 : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_nombre, _menhir_box_input) _menhir_cell1_instruction -> _ -> _menhir_box_input =
    fun _menhir_stack _v ->
      let MenhirCell1_instruction (_menhir_stack, _, i) = _menhir_stack in
      let MenhirCell1_nombre (_menhir_stack, _menhir_s, n) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_43 i n xs in
      _menhir_goto_separated_nonempty_list_CR___anonymous_0_ _menhir_stack _v _menhir_s
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let n = _v in
      let _v = _menhir_action_22 n in
      _menhir_goto_nombre _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_nombre : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState59 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState54 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState48 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState40 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState38 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState06 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState08 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState09 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState30 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState10 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState11 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState12 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState13 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState14 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState23 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState21 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState15 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState72 ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState00 ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_19 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let n = _v in
      let _v = _menhir_action_09 n in
      _menhir_goto_facteur _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_facteur : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState23 ->
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState21 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState59 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState54 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState48 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState40 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState38 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState06 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState08 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState09 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState30 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState10 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState11 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState12 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState13 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState14 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState15 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_24 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_DIV -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_DIV (_menhir_stack, _menhir_s) = _menhir_stack in
      let f = _v in
      let _v = _menhir_action_24 f in
      _menhir_goto_op_facteur_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_op_facteur_list : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_op_facteur_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | MULT ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
      | DIV ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
      | ALORS | COMMA | CR | EOF | EQ | GT | GTE | INT _ | LT | LTE | MOINS | NEQ | PD | PG | PLUS | VAR _ ->
          let _v_0 = _menhir_action_20 () in
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_21 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MULT (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState21 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_07 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let v = _v in
      let _v = _menhir_action_08 v in
      _menhir_goto_facteur _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_09 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PG (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState09 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | PLUS ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MOINS ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_08 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PLUS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState08 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_10 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MOINS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState10 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_23 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DIV (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState23 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_26 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_op_facteur_list -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_op_facteur_list (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_21 x xs in
      _menhir_goto_list_op_facteur_list_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_list_op_facteur_list_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState20 ->
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState25 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_27 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_facteur -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_facteur (_menhir_stack, _menhir_s, f) = _menhir_stack in
      let fl = _v in
      let _v = _menhir_action_44 f fl in
      _menhir_goto_terme _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_terme : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState08 ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState59 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState54 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState48 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState40 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState38 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState06 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState09 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState30 ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState11 ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState13 ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState15 ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState14 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState12 ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState10 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_34 : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_PLUS as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VAR _v_0 ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState34
      | PLUS ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState34
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState34
      | MOINS ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState34
      | INT _v_1 ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState34
      | _ ->
          _eRR ()
  
  and _menhir_run_12 : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_terme as 'stack) -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PLUS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState12 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_14 : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_terme as 'stack) -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MOINS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState14 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_30 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VAR _v_0 ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState30
      | PLUS ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | PG ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | MOINS ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | INT _v_1 ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState30
      | ALORS | COMMA | CR | EOF | EQ | GT | GTE | LT | LTE | NEQ | PD ->
          let t = _v in
          let _v = _menhir_action_04 t in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_expression : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState59 ->
          _menhir_run_57 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState54 ->
          _menhir_run_57 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState48 ->
          _menhir_run_49 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState40 ->
          _menhir_run_41 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState38 ->
          _menhir_run_39 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState06 ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState09 ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_57 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let e = _v in
      let _v = _menhir_action_03 e in
      _menhir_goto_expr_or_string _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr_or_string : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr_or_string (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState59 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR _v ->
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STRING _v ->
              _menhir_run_55 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | PLUS ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PG ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MOINS ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT _v ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | CR | EOF ->
          let x = _v in
          let _v = _menhir_action_38 x in
          _menhir_goto_separated_nonempty_list_COMMA_expr_or_string_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_55 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let s = _v in
      let _v = _menhir_action_02 s in
      _menhir_goto_expr_or_string _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_separated_nonempty_list_COMMA_expr_or_string_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState59 ->
          _menhir_run_60 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState54 ->
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_60 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_expr_or_string -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_or_string (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_39 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_expr_or_string_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_56 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_IMPRIME -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let l = _v in
      let _v = _menhir_action_01 l in
      let MenhirCell1_IMPRIME (_menhir_stack, _menhir_s) = _menhir_stack in
      let s = _v in
      let _v = _menhir_action_12 s in
      _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_instruction : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState05 ->
          _menhir_run_71 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState50 ->
          _menhir_run_70 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_71 : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_nombre as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | CR ->
          let _menhir_stack = MenhirCell1_instruction (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState72 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT _v ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | EOF ->
          let MenhirCell1_nombre (_menhir_stack, _menhir_s, n) = _menhir_stack in
          let i = _v in
          let _v = _menhir_action_42 i n in
          _menhir_goto_separated_nonempty_list_CR___anonymous_0_ _menhir_stack _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_70 : type  ttv_stack. (((ttv_stack, _menhir_box_input) _menhir_cell1_SI, _menhir_box_input) _menhir_cell1_expression _menhir_cell0_relop, _menhir_box_input) _menhir_cell1_expression -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expression (_menhir_stack, _, e2) = _menhir_stack in
      let MenhirCell0_relop (_menhir_stack, op) = _menhir_stack in
      let MenhirCell1_expression (_menhir_stack, _, e1) = _menhir_stack in
      let MenhirCell1_SI (_menhir_stack, _menhir_s) = _menhir_stack in
      let i = _v in
      let _v = _menhir_action_13 e1 e2 i op in
      _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_49 : type  ttv_stack. (((ttv_stack, _menhir_box_input) _menhir_cell1_SI, _menhir_box_input) _menhir_cell1_expression _menhir_cell0_relop as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ALORS ->
          let _menhir_s = MenhirState50 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAVERS ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | VAR _v ->
              _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | SI ->
              _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | REM ->
              _menhir_run_51 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NL ->
              _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IMPRIME ->
              _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FIN ->
              _menhir_run_62 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ENTREE ->
              _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_06 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_VAVERS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState06 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | PLUS ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MOINS ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_37 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_VAR (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _menhir_s = MenhirState38 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR _v ->
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | PLUS ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PG ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MOINS ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT _v ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_40 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_SI (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState40 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | PLUS ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MOINS ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_51 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let s = _v in
          let _v = _menhir_action_18 s in
          _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_53 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_19 () in
      _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_54 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IMPRIME (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState54 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STRING _v ->
          _menhir_run_55 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | PLUS ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MOINS ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_62 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_17 () in
      _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_63 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ENTREE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState63 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_64 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_64 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let v = _v in
      let _v = _menhir_action_45 v in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_var (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState67 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR _v ->
              _menhir_run_64 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | CR | EOF ->
          let x = _v in
          let _v = _menhir_action_40 x in
          _menhir_goto_separated_nonempty_list_COMMA_var_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_var_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState63 ->
          _menhir_run_69 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState67 ->
          _menhir_run_68 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_69 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_ENTREE -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let l = _v in
      let _v = _menhir_action_46 l in
      let MenhirCell1_ENTREE (_menhir_stack, _menhir_s) = _menhir_stack in
      let vs = _v in
      let _v = _menhir_action_15 vs in
      _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_68 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_var -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_var (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_41 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_var_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_41 : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_SI as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | NEQ ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_32 () in
          _menhir_goto_relop _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LTE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_33 () in
          _menhir_goto_relop _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | LT ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_goto_relop _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | GTE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_goto_relop _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | GT ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_goto_relop _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | EQ ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_37 () in
          _menhir_goto_relop _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_relop : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_SI, _menhir_box_input) _menhir_cell1_expression -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_relop (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | VAR _v_0 ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState48
      | PLUS ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState48
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState48
      | MOINS ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState48
      | INT _v_1 ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState48
      | _ ->
          _eRR ()
  
  and _menhir_run_39 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_VAR -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_VAR (_menhir_stack, _menhir_s, v) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_16 e v in
      _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_36 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_VAVERS -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_VAVERS (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_14 e in
      _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_32 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_PG -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | PD ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_PG (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_10 e in
          _menhir_goto_facteur _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_16 : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_terme as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let t = _v in
      let _v = _menhir_action_25 t in
      _menhir_goto_operateur_terme _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_operateur_terme : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_terme as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let op = _v in
      let _v = _menhir_action_28 op in
      _menhir_goto_operateur_terme_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_operateur_terme_list : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_terme as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState34 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState30 ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState11 ->
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState13 ->
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState15 ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_35 : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_PLUS, _menhir_box_input) _menhir_cell1_terme -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_terme (_menhir_stack, _, t) = _menhir_stack in
      let MenhirCell1_PLUS (_menhir_stack, _menhir_s) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_06 l t in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_31 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_terme -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_terme (_menhir_stack, _menhir_s, t) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_05 l t in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_29 : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_MOINS, _menhir_box_input) _menhir_cell1_terme -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_terme (_menhir_stack, _, t) = _menhir_stack in
      let MenhirCell1_MOINS (_menhir_stack, _menhir_s) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_07 l t in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_28 : type  ttv_stack. (((ttv_stack, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_cell1_PLUS, _menhir_box_input) _menhir_cell1_terme -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_terme (_menhir_stack, _, t) = _menhir_stack in
      let MenhirCell1_PLUS (_menhir_stack, _menhir_s) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_29 l t in
      _menhir_goto_operateur_terme_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_17 : type  ttv_stack. (((ttv_stack, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_cell1_MOINS, _menhir_box_input) _menhir_cell1_terme -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_terme (_menhir_stack, _, t) = _menhir_stack in
      let MenhirCell1_MOINS (_menhir_stack, _menhir_s) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_30 l t in
      _menhir_goto_operateur_terme_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_15 : type  ttv_stack. (((ttv_stack, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_cell1_MOINS as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VAR _v_0 ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState15
      | PLUS ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | PG ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | MOINS ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | INT _v_1 ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState15
      | ALORS | COMMA | CR | EOF | EQ | GT | GTE | LT | LTE | NEQ | PD ->
          let MenhirCell1_MOINS (_menhir_stack, _menhir_s) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_27 t in
          _menhir_goto_operateur_terme _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_13 : type  ttv_stack. (((ttv_stack, _menhir_box_input) _menhir_cell1_terme, _menhir_box_input) _menhir_cell1_PLUS as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VAR _v_0 ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState13
      | PLUS ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
      | PG ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
      | MOINS ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
      | INT _v_1 ->
          let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState13
      | ALORS | COMMA | CR | EOF | EQ | GT | GTE | LT | LTE | NEQ | PD ->
          let MenhirCell1_PLUS (_menhir_stack, _menhir_s) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_26 t in
          _menhir_goto_operateur_terme _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_11 : type  ttv_stack. ((ttv_stack, _menhir_box_input) _menhir_cell1_MOINS as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_terme (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VAR _v_0 ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState11
      | PLUS ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | PG ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | MOINS ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState11
      | INT _v_1 ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState11
      | _ ->
          _eRR ()
  
  and _menhir_run_22 : type  ttv_stack. (ttv_stack, _menhir_box_input) _menhir_cell1_MULT -> _ -> _ -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_MULT (_menhir_stack, _menhir_s) = _menhir_stack in
      let f = _v in
      let _v = _menhir_action_23 f in
      _menhir_goto_op_facteur_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_20 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_facteur (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | MULT ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState20
      | DIV ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState20
      | ALORS | COMMA | CR | EOF | EQ | GT | GTE | INT _ | LT | LTE | MOINS | NEQ | PD | PG | PLUS | VAR _ ->
          let _v_0 = _menhir_action_20 () in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_05 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_input) _menhir_state -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_nombre (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VAVERS ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | VAR _v_0 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState05
      | SI ->
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | REM ->
          _menhir_run_51 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | NL ->
          _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | IMPRIME ->
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | FIN ->
          _menhir_run_62 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | ENTREE ->
          _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | _ ->
          _eRR ()
  
  let _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_input =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState00 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | INT _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
end

let input =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_input v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
