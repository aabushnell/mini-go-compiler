
module MenhirBasics = struct
  
  exception Error = Parsing.Parse_error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | VERTICALBARVERTICALBAR
    | VAR
    | TYPE
    | STRUCT
    | STRING of (
# 11 "parser.mly"
       (string)
# 19 "parser.ml"
  )
    | STAR
    | SLASH
    | SEMICOLON
    | RIGHTPAR
    | RIGHTBRACE
    | RETURN
    | PLUSPLUS
    | PLUS
    | PERCENT
    | PACKAGE
    | NIL
    | MINUSMINUS
    | MINUS
    | LEFTPAR
    | LEFTBRACE
    | IMPORT
    | IF
    | IDENT of (
# 10 "parser.mly"
       (string)
# 41 "parser.ml"
  )
    | FUNC
    | FOR
    | EQ
    | EOF
    | ELSE
    | DOT
    | CST of (
# 9 "parser.mly"
       (Ast.constant)
# 52 "parser.ml"
  )
    | COMP of (
# 21 "parser.mly"
       (Ast.binop)
# 57 "parser.ml"
  )
    | COMMA
    | COLONEQ
    | BANG
    | AMPERSANDAMPERSAND
    | AMP
  
end

include MenhirBasics

# 4 "parser.mly"
  
  open Ast
  let mk_expr loc d = { pexpr_desc = d; pexpr_loc = loc }

# 74 "parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState001 : ('s, _menhir_box_file) _menhir_state
    (** State 001.
        Stack shape : .
        Start symbol: file. *)

  | MenhirState009 : (('s, _menhir_box_file) _menhir_cell1_ident_main _menhir_cell0_boption_import_fmt_, _menhir_box_file) _menhir_state
    (** State 009.
        Stack shape : ident_main boption(import_fmt).
        Start symbol: file. *)

  | MenhirState010 : (('s, _menhir_box_file) _menhir_cell1_TYPE, _menhir_box_file) _menhir_state
    (** State 010.
        Stack shape : TYPE.
        Start symbol: file. *)

  | MenhirState013 : ((('s, _menhir_box_file) _menhir_cell1_TYPE, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTBRACE, _menhir_box_file) _menhir_state
    (** State 013.
        Stack shape : TYPE ident LEFTBRACE.
        Start symbol: file. *)

  | MenhirState014 : (('s, _menhir_box_file) _menhir_cell1_separated_nonempty_list_COMMA_ident_, _menhir_box_file) _menhir_state
    (** State 014.
        Stack shape : separated_nonempty_list(COMMA,ident).
        Start symbol: file. *)

  | MenhirState015 : (('s, _menhir_box_file) _menhir_cell1_STAR, _menhir_box_file) _menhir_state
    (** State 015.
        Stack shape : STAR.
        Start symbol: file. *)

  | MenhirState023 : (('s, _menhir_box_file) _menhir_cell1_ids_and_type, _menhir_box_file) _menhir_state
    (** State 023.
        Stack shape : ids_and_type.
        Start symbol: file. *)

  | MenhirState025 : (('s, _menhir_box_file) _menhir_cell1_ident, _menhir_box_file) _menhir_state
    (** State 025.
        Stack shape : ident.
        Start symbol: file. *)

  | MenhirState030 : (('s, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_state
    (** State 030.
        Stack shape : FUNC.
        Start symbol: file. *)

  | MenhirState032 : ((('s, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR, _menhir_box_file) _menhir_state
    (** State 032.
        Stack shape : FUNC ident LEFTPAR.
        Start symbol: file. *)

  | MenhirState035 : (((('s, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR, _menhir_box_file) _menhir_cell1_loption_parameters_ _menhir_cell0_RIGHTPAR, _menhir_box_file) _menhir_state
    (** State 035.
        Stack shape : FUNC ident LEFTPAR loption(parameters) RIGHTPAR.
        Start symbol: file. *)

  | MenhirState036 : ((((('s, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR, _menhir_box_file) _menhir_cell1_loption_parameters_ _menhir_cell0_RIGHTPAR, _menhir_box_file) _menhir_cell1_LEFTPAR, _menhir_box_file) _menhir_state
    (** State 036.
        Stack shape : FUNC ident LEFTPAR loption(parameters) RIGHTPAR LEFTPAR.
        Start symbol: file. *)

  | MenhirState037 : (('s, _menhir_box_file) _menhir_cell1_type_expr, _menhir_box_file) _menhir_state
    (** State 037.
        Stack shape : type_expr.
        Start symbol: file. *)

  | MenhirState038 : ((('s, _menhir_box_file) _menhir_cell1_type_expr, _menhir_box_file) _menhir_cell1_COMMA, _menhir_box_file) _menhir_state
    (** State 038.
        Stack shape : type_expr COMMA.
        Start symbol: file. *)

  | MenhirState045 : ((((('s, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR, _menhir_box_file) _menhir_cell1_loption_parameters_ _menhir_cell0_RIGHTPAR, _menhir_box_file) _menhir_cell1_loption_return_type_, _menhir_box_file) _menhir_state
    (** State 045.
        Stack shape : FUNC ident LEFTPAR loption(parameters) RIGHTPAR loption(return_type).
        Start symbol: file. *)

  | MenhirState046 : (('s, _menhir_box_file) _menhir_cell1_LEFTBRACE, _menhir_box_file) _menhir_state
    (** State 046.
        Stack shape : LEFTBRACE.
        Start symbol: file. *)

  | MenhirState047 : (('s, _menhir_box_file) _menhir_cell1_VAR, _menhir_box_file) _menhir_state
    (** State 047.
        Stack shape : VAR.
        Start symbol: file. *)

  | MenhirState048 : ((('s, _menhir_box_file) _menhir_cell1_VAR, _menhir_box_file) _menhir_cell1_separated_nonempty_list_COMMA_ident_, _menhir_box_file) _menhir_state
    (** State 048.
        Stack shape : VAR separated_nonempty_list(COMMA,ident).
        Start symbol: file. *)

  | MenhirState051 : (((('s, _menhir_box_file) _menhir_cell1_VAR, _menhir_box_file) _menhir_cell1_separated_nonempty_list_COMMA_ident_, _menhir_box_file) _menhir_cell1_option_type_expr_, _menhir_box_file) _menhir_state
    (** State 051.
        Stack shape : VAR separated_nonempty_list(COMMA,ident) option(type_expr).
        Start symbol: file. *)

  | MenhirState053 : (('s, _menhir_box_file) _menhir_cell1_STAR, _menhir_box_file) _menhir_state
    (** State 053.
        Stack shape : STAR.
        Start symbol: file. *)

  | MenhirState055 : (('s, _menhir_box_file) _menhir_cell1_MINUS, _menhir_box_file) _menhir_state
    (** State 055.
        Stack shape : MINUS.
        Start symbol: file. *)

  | MenhirState056 : (('s, _menhir_box_file) _menhir_cell1_LEFTPAR, _menhir_box_file) _menhir_state
    (** State 056.
        Stack shape : LEFTPAR.
        Start symbol: file. *)

  | MenhirState058 : (('s, _menhir_box_file) _menhir_cell1_BANG, _menhir_box_file) _menhir_state
    (** State 058.
        Stack shape : BANG.
        Start symbol: file. *)

  | MenhirState059 : (('s, _menhir_box_file) _menhir_cell1_AMP, _menhir_box_file) _menhir_state
    (** State 059.
        Stack shape : AMP.
        Start symbol: file. *)

  | MenhirState060 : (('s, _menhir_box_file) _menhir_cell1_ident, _menhir_box_file) _menhir_state
    (** State 060.
        Stack shape : ident.
        Start symbol: file. *)

  | MenhirState061 : ((('s, _menhir_box_file) _menhir_cell1_ident, _menhir_box_file) _menhir_cell1_LEFTPAR, _menhir_box_file) _menhir_state
    (** State 061.
        Stack shape : ident LEFTPAR.
        Start symbol: file. *)

  | MenhirState066 : (('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 066.
        Stack shape : expr.
        Start symbol: file. *)

  | MenhirState067 : ((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_VERTICALBARVERTICALBAR, _menhir_box_file) _menhir_state
    (** State 067.
        Stack shape : expr VERTICALBARVERTICALBAR.
        Start symbol: file. *)

  | MenhirState068 : (((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_VERTICALBARVERTICALBAR, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 068.
        Stack shape : expr VERTICALBARVERTICALBAR expr.
        Start symbol: file. *)

  | MenhirState069 : ((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_STAR, _menhir_box_file) _menhir_state
    (** State 069.
        Stack shape : expr STAR.
        Start symbol: file. *)

  | MenhirState070 : (((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_STAR, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 070.
        Stack shape : expr STAR expr.
        Start symbol: file. *)

  | MenhirState071 : ((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_DOT, _menhir_box_file) _menhir_state
    (** State 071.
        Stack shape : expr DOT.
        Start symbol: file. *)

  | MenhirState072 : (((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_DOT, _menhir_box_file) _menhir_cell1_ident, _menhir_box_file) _menhir_state
    (** State 072.
        Stack shape : expr DOT ident.
        Start symbol: file. *)

  | MenhirState074 : ((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_SLASH, _menhir_box_file) _menhir_state
    (** State 074.
        Stack shape : expr SLASH.
        Start symbol: file. *)

  | MenhirState075 : (((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_SLASH, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 075.
        Stack shape : expr SLASH expr.
        Start symbol: file. *)

  | MenhirState076 : ((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_PLUS, _menhir_box_file) _menhir_state
    (** State 076.
        Stack shape : expr PLUS.
        Start symbol: file. *)

  | MenhirState077 : (((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_PLUS, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 077.
        Stack shape : expr PLUS expr.
        Start symbol: file. *)

  | MenhirState078 : ((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_PERCENT, _menhir_box_file) _menhir_state
    (** State 078.
        Stack shape : expr PERCENT.
        Start symbol: file. *)

  | MenhirState079 : (((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_PERCENT, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 079.
        Stack shape : expr PERCENT expr.
        Start symbol: file. *)

  | MenhirState080 : ((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_MINUS, _menhir_box_file) _menhir_state
    (** State 080.
        Stack shape : expr MINUS.
        Start symbol: file. *)

  | MenhirState081 : (((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_MINUS, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 081.
        Stack shape : expr MINUS expr.
        Start symbol: file. *)

  | MenhirState082 : ((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_COMP, _menhir_box_file) _menhir_state
    (** State 082.
        Stack shape : expr COMP.
        Start symbol: file. *)

  | MenhirState083 : (((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_COMP, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 083.
        Stack shape : expr COMP expr.
        Start symbol: file. *)

  | MenhirState084 : ((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_AMPERSANDAMPERSAND, _menhir_box_file) _menhir_state
    (** State 084.
        Stack shape : expr AMPERSANDAMPERSAND.
        Start symbol: file. *)

  | MenhirState085 : (((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_AMPERSANDAMPERSAND, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 085.
        Stack shape : expr AMPERSANDAMPERSAND expr.
        Start symbol: file. *)

  | MenhirState086 : ((('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_COMMA, _menhir_box_file) _menhir_state
    (** State 086.
        Stack shape : expr COMMA.
        Start symbol: file. *)

  | MenhirState089 : ((('s, _menhir_box_file) _menhir_cell1_AMP, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 089.
        Stack shape : AMP expr.
        Start symbol: file. *)

  | MenhirState090 : ((('s, _menhir_box_file) _menhir_cell1_BANG, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 090.
        Stack shape : BANG expr.
        Start symbol: file. *)

  | MenhirState091 : ((('s, _menhir_box_file) _menhir_cell1_LEFTPAR, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 091.
        Stack shape : LEFTPAR expr.
        Start symbol: file. *)

  | MenhirState093 : ((('s, _menhir_box_file) _menhir_cell1_MINUS, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 093.
        Stack shape : MINUS expr.
        Start symbol: file. *)

  | MenhirState094 : ((('s, _menhir_box_file) _menhir_cell1_STAR, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 094.
        Stack shape : STAR expr.
        Start symbol: file. *)

  | MenhirState099 : (('s, _menhir_box_file) _menhir_cell1_SEMICOLON, _menhir_box_file) _menhir_state
    (** State 099.
        Stack shape : SEMICOLON.
        Start symbol: file. *)

  | MenhirState100 : (('s, _menhir_box_file) _menhir_cell1_RETURN, _menhir_box_file) _menhir_state
    (** State 100.
        Stack shape : RETURN.
        Start symbol: file. *)

  | MenhirState102 : (('s, _menhir_box_file) _menhir_cell1_IF, _menhir_box_file) _menhir_state
    (** State 102.
        Stack shape : IF.
        Start symbol: file. *)

  | MenhirState103 : ((('s, _menhir_box_file) _menhir_cell1_IF, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 103.
        Stack shape : IF expr.
        Start symbol: file. *)

  | MenhirState105 : (((('s, _menhir_box_file) _menhir_cell1_IF, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_block, _menhir_box_file) _menhir_state
    (** State 105.
        Stack shape : IF expr block.
        Start symbol: file. *)

  | MenhirState109 : (('s, _menhir_box_file) _menhir_cell1_FOR, _menhir_box_file) _menhir_state
    (** State 109.
        Stack shape : FOR.
        Start symbol: file. *)

  | MenhirState113 : ((('s, _menhir_box_file) _menhir_cell1_FOR, _menhir_box_file) _menhir_cell1_opt_simple_stmt, _menhir_box_file) _menhir_state
    (** State 113.
        Stack shape : FOR opt_simple_stmt.
        Start symbol: file. *)

  | MenhirState114 : (((('s, _menhir_box_file) _menhir_cell1_FOR, _menhir_box_file) _menhir_cell1_opt_simple_stmt, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 114.
        Stack shape : FOR opt_simple_stmt expr.
        Start symbol: file. *)

  | MenhirState115 : ((((('s, _menhir_box_file) _menhir_cell1_FOR, _menhir_box_file) _menhir_cell1_opt_simple_stmt, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_SEMICOLON, _menhir_box_file) _menhir_state
    (** State 115.
        Stack shape : FOR opt_simple_stmt expr SEMICOLON.
        Start symbol: file. *)

  | MenhirState116 : (((((('s, _menhir_box_file) _menhir_cell1_FOR, _menhir_box_file) _menhir_cell1_opt_simple_stmt, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_SEMICOLON, _menhir_box_file) _menhir_cell1_opt_simple_stmt, _menhir_box_file) _menhir_state
    (** State 116.
        Stack shape : FOR opt_simple_stmt expr SEMICOLON opt_simple_stmt.
        Start symbol: file. *)

  | MenhirState119 : (('s, _menhir_box_file) _menhir_cell1_exprs, _menhir_box_file) _menhir_state
    (** State 119.
        Stack shape : exprs.
        Start symbol: file. *)

  | MenhirState121 : (('s, _menhir_box_file) _menhir_cell1_exprs, _menhir_box_file) _menhir_state
    (** State 121.
        Stack shape : exprs.
        Start symbol: file. *)

  | MenhirState123 : (('s, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 123.
        Stack shape : expr.
        Start symbol: file. *)

  | MenhirState127 : ((('s, _menhir_box_file) _menhir_cell1_FOR, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_state
    (** State 127.
        Stack shape : FOR expr.
        Start symbol: file. *)

  | MenhirState132 : (('s, _menhir_box_file) _menhir_cell1_stmt, _menhir_box_file) _menhir_state
    (** State 132.
        Stack shape : stmt.
        Start symbol: file. *)

  | MenhirState143 : (('s, _menhir_box_file) _menhir_cell1_ids_and_type, _menhir_box_file) _menhir_state
    (** State 143.
        Stack shape : ids_and_type.
        Start symbol: file. *)

  | MenhirState144 : ((('s, _menhir_box_file) _menhir_cell1_ids_and_type, _menhir_box_file) _menhir_cell1_COMMA, _menhir_box_file) _menhir_state
    (** State 144.
        Stack shape : ids_and_type COMMA.
        Start symbol: file. *)

  | MenhirState149 : (('s, _menhir_box_file) _menhir_cell1_decl, _menhir_box_file) _menhir_state
    (** State 149.
        Stack shape : decl.
        Start symbol: file. *)


and ('s, 'r) _menhir_cell1_block = 
  | MenhirCell1_block of 's * ('s, 'r) _menhir_state * (Ast.pexpr) * Lexing.position

and 's _menhir_cell0_boption_import_fmt_ = 
  | MenhirCell0_boption_import_fmt_ of 's * (bool)

and ('s, 'r) _menhir_cell1_decl = 
  | MenhirCell1_decl of 's * ('s, 'r) _menhir_state * (Ast.pdecl)

and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Ast.pexpr) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_exprs = 
  | MenhirCell1_exprs of 's * ('s, 'r) _menhir_state * (Ast.pexpr list) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_ident = 
  | MenhirCell1_ident of 's * ('s, 'r) _menhir_state * (Ast.ident) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_ident_main = 
  | MenhirCell1_ident_main of 's * ('s, 'r) _menhir_state * (unit)

and ('s, 'r) _menhir_cell1_ids_and_type = 
  | MenhirCell1_ids_and_type of 's * ('s, 'r) _menhir_state * (Ast.pfield list)

and ('s, 'r) _menhir_cell1_loption_parameters_ = 
  | MenhirCell1_loption_parameters_ of 's * ('s, 'r) _menhir_state * (Ast.pfield list list)

and ('s, 'r) _menhir_cell1_loption_return_type_ = 
  | MenhirCell1_loption_return_type_ of 's * ('s, 'r) _menhir_state * (Ast.ptyp list)

and ('s, 'r) _menhir_cell1_opt_simple_stmt = 
  | MenhirCell1_opt_simple_stmt of 's * ('s, 'r) _menhir_state * (Ast.pexpr)

and ('s, 'r) _menhir_cell1_option_type_expr_ = 
  | MenhirCell1_option_type_expr_ of 's * ('s, 'r) _menhir_state * (Ast.ptyp option)

and ('s, 'r) _menhir_cell1_separated_nonempty_list_COMMA_ident_ = 
  | MenhirCell1_separated_nonempty_list_COMMA_ident_ of 's * ('s, 'r) _menhir_state * (Ast.ident list)

and ('s, 'r) _menhir_cell1_stmt = 
  | MenhirCell1_stmt of 's * ('s, 'r) _menhir_state * (Ast.pexpr)

and ('s, 'r) _menhir_cell1_type_expr = 
  | MenhirCell1_type_expr of 's * ('s, 'r) _menhir_state * (Ast.ptyp)

and ('s, 'r) _menhir_cell1_AMP = 
  | MenhirCell1_AMP of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_AMPERSANDAMPERSAND = 
  | MenhirCell1_AMPERSANDAMPERSAND of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_BANG = 
  | MenhirCell1_BANG of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_COMMA = 
  | MenhirCell1_COMMA of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_COMP = 
  | MenhirCell1_COMP of 's * ('s, 'r) _menhir_state * (
# 21 "parser.mly"
       (Ast.binop)
# 484 "parser.ml"
)

and ('s, 'r) _menhir_cell1_DOT = 
  | MenhirCell1_DOT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_FOR = 
  | MenhirCell1_FOR of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_FUNC = 
  | MenhirCell1_FUNC of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_LEFTBRACE = 
  | MenhirCell1_LEFTBRACE of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_LEFTBRACE = 
  | MenhirCell0_LEFTBRACE of 's * Lexing.position

and ('s, 'r) _menhir_cell1_LEFTPAR = 
  | MenhirCell1_LEFTPAR of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_LEFTPAR = 
  | MenhirCell0_LEFTPAR of 's * Lexing.position

and ('s, 'r) _menhir_cell1_MINUS = 
  | MenhirCell1_MINUS of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_PERCENT = 
  | MenhirCell1_PERCENT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PLUS = 
  | MenhirCell1_PLUS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_RETURN = 
  | MenhirCell1_RETURN of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_RIGHTPAR = 
  | MenhirCell0_RIGHTPAR of 's * Lexing.position

and ('s, 'r) _menhir_cell1_SEMICOLON = 
  | MenhirCell1_SEMICOLON of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_SLASH = 
  | MenhirCell1_SLASH of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_STAR = 
  | MenhirCell1_STAR of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_TYPE = 
  | MenhirCell1_TYPE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_VAR = 
  | MenhirCell1_VAR of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_VERTICALBARVERTICALBAR = 
  | MenhirCell1_VERTICALBARVERTICALBAR of 's * ('s, 'r) _menhir_state

and _menhir_box_file = 
  | MenhirBox_file of (Ast.pfile) [@@unboxed]

let _menhir_action_01 =
  fun xs ->
    let l = 
# 241 "<standard.mly>"
    ( xs )
# 552 "parser.ml"
     in
    (
# 226 "parser.mly"
  ( l )
# 557 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_02 =
  fun _endpos__2_ _startpos__1_ ->
    let _endpos = _endpos__2_ in
    let _startpos = _startpos__1_ in
    (
# 98 "parser.mly"
  ( { pexpr_desc = PEblock []; pexpr_loc = _startpos, _endpos } )
# 567 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_03 =
  fun _endpos__3_ _startpos__1_ l ->
    let _endpos = _endpos__3_ in
    let _startpos = _startpos__1_ in
    (
# 100 "parser.mly"
  ( { pexpr_desc = PEblock l; pexpr_loc = _startpos, _endpos } )
# 577 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_04 =
  fun () ->
    (
# 134 "<standard.mly>"
    ( false )
# 585 "parser.ml"
     : (bool))

let _menhir_action_05 =
  fun () ->
    (
# 137 "<standard.mly>"
    ( true )
# 593 "parser.ml"
     : (bool))

let _menhir_action_06 =
  fun b id pl ty ->
    (
# 57 "parser.mly"
  ( PDfunction { pf_name = id;
                 pf_params = List.flatten pl;
                 pf_typ = ty;
                 pf_body = b } )
# 604 "parser.ml"
     : (Ast.pdecl))

let _menhir_action_07 =
  fun fl id ->
    (
# 62 "parser.mly"
  ( PDstruct { ps_name = id; ps_fields = List.flatten fl; } )
# 612 "parser.ml"
     : (Ast.pdecl))

let _menhir_action_08 =
  fun _endpos_d_ _startpos_d_ d ->
    let _endpos = _endpos_d_ in
    let _startpos = _startpos_d_ in
    (
# 190 "parser.mly"
  ( { pexpr_desc = d; pexpr_loc = _startpos, _endpos } )
# 622 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_09 =
  fun c ->
    (
# 195 "parser.mly"
    ( PEconstant c )
# 630 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_10 =
  fun s ->
    (
# 197 "parser.mly"
    ( PEconstant (Cstring s) )
# 638 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_11 =
  fun () ->
    (
# 199 "parser.mly"
    ( PEnil )
# 646 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_12 =
  fun e ->
    (
# 201 "parser.mly"
  ( e.pexpr_desc )
# 654 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_13 =
  fun id ->
    (
# 203 "parser.mly"
   ( PEident id )
# 662 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_14 =
  fun e id ->
    (
# 205 "parser.mly"
   ( PEdot (e, id) )
# 670 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_15 =
  fun el id ->
    (
# 207 "parser.mly"
   ( PEcall (id, el) )
# 678 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_16 =
  fun e el id ->
    (
# 209 "parser.mly"
   ( match e.pexpr_desc, id.id with
     | PEident {id="fmt"}, "Print" -> PEcall ({id with id = "fmt.Print"}, el)
     | _ -> raise Parsing.Parse_error )
# 688 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_17 =
  fun e1 e2 ->
    let op = 
# 230 "parser.mly"
             ( Badd )
# 696 "parser.ml"
     in
    (
# 213 "parser.mly"
  ( PEbinop (op, e1, e2) )
# 701 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_18 =
  fun e1 e2 ->
    let op = 
# 231 "parser.mly"
             ( Bsub )
# 709 "parser.ml"
     in
    (
# 213 "parser.mly"
  ( PEbinop (op, e1, e2) )
# 714 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_19 =
  fun e1 e2 ->
    let op = 
# 232 "parser.mly"
             ( Bmul )
# 722 "parser.ml"
     in
    (
# 213 "parser.mly"
  ( PEbinop (op, e1, e2) )
# 727 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_20 =
  fun e1 e2 ->
    let op = 
# 233 "parser.mly"
             ( Bdiv )
# 735 "parser.ml"
     in
    (
# 213 "parser.mly"
  ( PEbinop (op, e1, e2) )
# 740 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_21 =
  fun e1 e2 ->
    let op = 
# 234 "parser.mly"
             ( Bmod )
# 748 "parser.ml"
     in
    (
# 213 "parser.mly"
  ( PEbinop (op, e1, e2) )
# 753 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_22 =
  fun c e1 e2 ->
    let op = 
# 235 "parser.mly"
             ( c )
# 761 "parser.ml"
     in
    (
# 213 "parser.mly"
  ( PEbinop (op, e1, e2) )
# 766 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_23 =
  fun e1 e2 ->
    let op = 
# 236 "parser.mly"
                           ( Band )
# 774 "parser.ml"
     in
    (
# 213 "parser.mly"
  ( PEbinop (op, e1, e2) )
# 779 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_24 =
  fun e1 e2 ->
    let op = 
# 237 "parser.mly"
                           ( Bor  )
# 787 "parser.ml"
     in
    (
# 213 "parser.mly"
  ( PEbinop (op, e1, e2) )
# 792 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_25 =
  fun e1 ->
    (
# 215 "parser.mly"
  ( PEunop (Unot, e1) )
# 800 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_26 =
  fun e1 ->
    (
# 217 "parser.mly"
  ( PEunop (Uneg, e1) )
# 808 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_27 =
  fun e1 ->
    (
# 219 "parser.mly"
  ( PEunop (Uamp, e1) )
# 816 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_28 =
  fun e1 ->
    (
# 221 "parser.mly"
  ( PEunop (Ustar, e1) )
# 824 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_29 =
  fun el ->
    (
# 185 "parser.mly"
                                            ( el )
# 832 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_30 =
  fun x ->
    (
# 66 "parser.mly"
                                           ( [x]     )
# 840 "parser.ml"
     : (Ast.pfield list list))

let _menhir_action_31 =
  fun x xl ->
    (
# 67 "parser.mly"
                                           ( x :: xl )
# 848 "parser.ml"
     : (Ast.pfield list list))

let _menhir_action_32 =
  fun dl imp ->
    (
# 42 "parser.mly"
  ( imp, dl )
# 856 "parser.ml"
     : (Ast.pfile))

let _menhir_action_33 =
  fun _endpos_id_ _startpos_id_ id ->
    let _endpos = _endpos_id_ in
    let _startpos = _startpos_id_ in
    (
# 241 "parser.mly"
             ( { loc = _startpos, _endpos; id = id } )
# 866 "parser.ml"
     : (Ast.ident))

let _menhir_action_34 =
  fun id ->
    (
# 46 "parser.mly"
             ( if id.id <> "main" then raise Parsing.Parse_error )
# 874 "parser.ml"
     : (unit))

let _menhir_action_35 =
  fun ids ty ->
    (
# 76 "parser.mly"
   ( List.map (fun x -> x, ty) ids )
# 882 "parser.ml"
     : (Ast.pfield list))

let _menhir_action_36 =
  fun _endpos_d_ _startpos_d_ d ->
    let _endpos = _endpos_d_ in
    let _startpos = _startpos_d_ in
    (
# 143 "parser.mly"
    ( { pexpr_desc = d; pexpr_loc = _startpos, _endpos } )
# 892 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_37 =
  fun _endpos_s_ _startpos__1_ e s ->
    let _endpos = _endpos_s_ in
    let _startpos = _startpos__1_ in
    (
# 148 "parser.mly"
  ( PEif (e, s, { pexpr_desc = PEskip; pexpr_loc = _startpos, _endpos }) )
# 902 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_38 =
  fun e s1 s2 ->
    (
# 150 "parser.mly"
  ( PEif (e, s1, s2) )
# 910 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_39 =
  fun e s1 s2 ->
    (
# 152 "parser.mly"
  ( PEif (e, s1, s2) )
# 918 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_40 =
  fun s ->
    (
# 50 "parser.mly"
                            ( if s <> "fmt" then raise Parsing.Parse_error )
# 926 "parser.ml"
     : (unit))

let _menhir_action_41 =
  fun () ->
    (
# 180 "parser.mly"
             ( Inc )
# 934 "parser.ml"
     : (Ast.incdec))

let _menhir_action_42 =
  fun () ->
    (
# 181 "parser.mly"
             ( Dec )
# 942 "parser.ml"
     : (Ast.incdec))

let _menhir_action_43 =
  fun el ->
    (
# 155 "parser.mly"
              ( el )
# 950 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_44 =
  fun () ->
    (
# 216 "<standard.mly>"
    ( [] )
# 958 "parser.ml"
     : (Ast.pdecl list))

let _menhir_action_45 =
  fun x xs ->
    (
# 219 "<standard.mly>"
    ( x :: xs )
# 966 "parser.ml"
     : (Ast.pdecl list))

let _menhir_action_46 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 974 "parser.ml"
     : (Ast.pfield list list))

let _menhir_action_47 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 982 "parser.ml"
     : (Ast.pfield list list))

let _menhir_action_48 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 990 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_49 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 998 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_50 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1006 "parser.ml"
     : (Ast.pfield list list))

let _menhir_action_51 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1014 "parser.ml"
     : (Ast.pfield list list))

let _menhir_action_52 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1022 "parser.ml"
     : (Ast.ptyp list))

let _menhir_action_53 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1030 "parser.ml"
     : (Ast.ptyp list))

let _menhir_action_54 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1038 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_55 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1046 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_56 =
  fun _endpos__0_ ->
    let _endpos = _endpos__0_ in
    let _startpos = _endpos__0_ in
    (
# 159 "parser.mly"
                  ( { pexpr_desc = PEskip; pexpr_loc = _startpos, _endpos } )
# 1056 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_57 =
  fun s ->
    (
# 160 "parser.mly"
                  ( s )
# 1064 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_58 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 1072 "parser.ml"
     : (unit option))

let _menhir_action_59 =
  fun x ->
    (
# 114 "<standard.mly>"
    ( Some x )
# 1080 "parser.ml"
     : (unit option))

let _menhir_action_60 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 1088 "parser.ml"
     : (unit option))

let _menhir_action_61 =
  fun x ->
    (
# 114 "<standard.mly>"
    ( Some x )
# 1096 "parser.ml"
     : (unit option))

let _menhir_action_62 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 1104 "parser.ml"
     : (Ast.ptyp option))

let _menhir_action_63 =
  fun x ->
    (
# 114 "<standard.mly>"
    ( Some x )
# 1112 "parser.ml"
     : (Ast.ptyp option))

let _menhir_action_64 =
  fun x ->
    (
# 70 "parser.mly"
                                           ( [x]     )
# 1120 "parser.ml"
     : (Ast.pfield list list))

let _menhir_action_65 =
  fun x xl ->
    (
# 71 "parser.mly"
                                           ( x :: xl )
# 1128 "parser.ml"
     : (Ast.pfield list list))

let _menhir_action_66 =
  fun ty ->
    (
# 80 "parser.mly"
                                               ( [ty] )
# 1136 "parser.ml"
     : (Ast.ptyp list))

let _menhir_action_67 =
  fun tyl ->
    (
# 81 "parser.mly"
                                      ( tyl )
# 1144 "parser.ml"
     : (Ast.ptyp list))

let _menhir_action_68 =
  fun ty ->
    (
# 85 "parser.mly"
                                            ( [ty] )
# 1152 "parser.ml"
     : (Ast.ptyp list))

let _menhir_action_69 =
  fun ty tyl ->
    (
# 86 "parser.mly"
                                            ( ty :: tyl )
# 1160 "parser.ml"
     : (Ast.ptyp list))

let _menhir_action_70 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1168 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_71 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1176 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_72 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1184 "parser.ml"
     : (Ast.ident list))

let _menhir_action_73 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1192 "parser.ml"
     : (Ast.ident list))

let _menhir_action_74 =
  fun e ->
    (
# 165 "parser.mly"
  ( e )
# 1200 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_75 =
  fun _endpos_d_ _startpos_d_ d ->
    let _endpos = _endpos_d_ in
    let _startpos = _startpos_d_ in
    (
# 167 "parser.mly"
  ( { pexpr_desc = d; pexpr_loc = _startpos, _endpos } )
# 1210 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_76 =
  fun el lvl ->
    (
# 171 "parser.mly"
  ( PEassign (lvl, el) )
# 1218 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_77 =
  fun el lvl ->
    (
# 173 "parser.mly"
  ( let var = function {pexpr_desc=PEident id} -> id | _ -> raise Parsing.Parse_error in
    PEvars (List.map var lvl, None, el) )
# 1227 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_78 =
  fun e i ->
    (
# 176 "parser.mly"
  ( PEincdec (e, i) )
# 1235 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_79 =
  fun s ->
    (
# 104 "parser.mly"
                                ( [s]    )
# 1243 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_80 =
  fun s ->
    (
# 105 "parser.mly"
                                ( [s]    )
# 1251 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_81 =
  fun l s ->
    (
# 106 "parser.mly"
                                ( s :: l )
# 1259 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_82 =
  fun l ->
    (
# 107 "parser.mly"
                                ( l      )
# 1267 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_83 =
  fun () ->
    (
# 108 "parser.mly"
                                ( []     )
# 1275 "parser.ml"
     : (Ast.pexpr list))

let _menhir_action_84 =
  fun s ->
    (
# 113 "parser.mly"
    ( s )
# 1283 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_85 =
  fun b ->
    (
# 115 "parser.mly"
    ( b )
# 1291 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_86 =
  fun s ->
    (
# 117 "parser.mly"
    ( s )
# 1299 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_87 =
  fun _endpos_d_ _startpos_d_ d ->
    let _endpos = _endpos_d_ in
    let _startpos = _startpos_d_ in
    (
# 119 "parser.mly"
    ( { pexpr_desc = d; pexpr_loc = _startpos, _endpos } )
# 1309 "parser.ml"
     : (Ast.pexpr))

let _menhir_action_88 =
  fun i ids ty ->
    (
# 125 "parser.mly"
  ( PEvars (ids, ty, i) )
# 1317 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_89 =
  fun xs ->
    let el = 
# 241 "<standard.mly>"
    ( xs )
# 1325 "parser.ml"
     in
    (
# 127 "parser.mly"
  ( PEreturn el )
# 1330 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_90 =
  fun _endpos_b_ _startpos__1_ b ->
    let _endpos = _endpos_b_ in
    let _startpos = _startpos__1_ in
    (
# 129 "parser.mly"
  ( let loc = _startpos, _endpos in
    let etrue = mk_expr loc (PEconstant (Cbool true)) in
    PEfor (etrue, b) )
# 1342 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_91 =
  fun b e1 ->
    (
# 133 "parser.mly"
  ( PEfor (e1, b) )
# 1350 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_92 =
  fun _endpos_b_ _startpos__1_ b e2 s1 s3 ->
    let _endpos = _endpos_b_ in
    let _startpos = _startpos__1_ in
    (
# 136 "parser.mly"
  ( let loc = _startpos, _endpos in
    let b = mk_expr loc (PEblock [b; s3]) in
    PEblock [s1; mk_expr loc (PEfor (e2, b))] )
# 1362 "parser.ml"
     : (Ast.pexpr_desc))

let _menhir_action_93 =
  fun id ->
    (
# 91 "parser.mly"
   ( PTident id )
# 1370 "parser.ml"
     : (Ast.ptyp))

let _menhir_action_94 =
  fun ty ->
    (
# 93 "parser.mly"
   ( PTptr ty )
# 1378 "parser.ml"
     : (Ast.ptyp))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | AMP ->
        "AMP"
    | AMPERSANDAMPERSAND ->
        "AMPERSANDAMPERSAND"
    | BANG ->
        "BANG"
    | COLONEQ ->
        "COLONEQ"
    | COMMA ->
        "COMMA"
    | COMP _ ->
        "COMP"
    | CST _ ->
        "CST"
    | DOT ->
        "DOT"
    | ELSE ->
        "ELSE"
    | EOF ->
        "EOF"
    | EQ ->
        "EQ"
    | FOR ->
        "FOR"
    | FUNC ->
        "FUNC"
    | IDENT _ ->
        "IDENT"
    | IF ->
        "IF"
    | IMPORT ->
        "IMPORT"
    | LEFTBRACE ->
        "LEFTBRACE"
    | LEFTPAR ->
        "LEFTPAR"
    | MINUS ->
        "MINUS"
    | MINUSMINUS ->
        "MINUSMINUS"
    | NIL ->
        "NIL"
    | PACKAGE ->
        "PACKAGE"
    | PERCENT ->
        "PERCENT"
    | PLUS ->
        "PLUS"
    | PLUSPLUS ->
        "PLUSPLUS"
    | RETURN ->
        "RETURN"
    | RIGHTBRACE ->
        "RIGHTBRACE"
    | RIGHTPAR ->
        "RIGHTPAR"
    | SEMICOLON ->
        "SEMICOLON"
    | SLASH ->
        "SLASH"
    | STAR ->
        "STAR"
    | STRING _ ->
        "STRING"
    | STRUCT ->
        "STRUCT"
    | TYPE ->
        "TYPE"
    | VAR ->
        "VAR"
    | VERTICALBARVERTICALBAR ->
        "VERTICALBARVERTICALBAR"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_147 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_ident_main _menhir_cell0_boption_import_fmt_ -> _ -> _menhir_box_file =
    fun _menhir_stack _v ->
      let MenhirCell0_boption_import_fmt_ (_menhir_stack, imp) = _menhir_stack in
      let MenhirCell1_ident_main (_menhir_stack, _, _) = _menhir_stack in
      let dl = _v in
      let _v = _menhir_action_32 dl imp in
      MenhirBox_file _v
  
  let rec _menhir_run_150 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_decl -> _ -> _menhir_box_file =
    fun _menhir_stack _v ->
      let MenhirCell1_decl (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_45 x xs in
      _menhir_goto_list_decl_ _menhir_stack _v _menhir_s
  
  and _menhir_goto_list_decl_ : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState149 ->
          _menhir_run_150 _menhir_stack _v
      | MenhirState009 ->
          _menhir_run_147 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_002 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos_id_, _startpos_id_, id) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_33 _endpos_id_ _startpos_id_ id in
      _menhir_goto_ident _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_id_ _startpos_id_ _v _menhir_s _tok
  
  and _menhir_goto_ident : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState001 ->
          _menhir_run_151 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState071 ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState046 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState099 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState132 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState109 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState100 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState086 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState084 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState082 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState080 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState069 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState067 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState061 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState030 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState032 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState144 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState047 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState025 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState023 ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState035 ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState048 ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState036 ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState038 ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState014 ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState015 ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState010 ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_151 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let id = _v in
      let _v = _menhir_action_34 id in
      let _menhir_stack = MenhirCell1_ident_main (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IMPORT ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | STRING _v_0 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | SEMICOLON ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let s = _v_0 in
                      let _ = _menhir_action_40 s in
                      let _v = _menhir_action_05 () in
                      _menhir_goto_boption_import_fmt_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | EOF | FUNC | TYPE ->
              let _v = _menhir_action_04 () in
              _menhir_goto_boption_import_fmt_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_boption_import_fmt_ : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_ident_main -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_boption_import_fmt_ (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | TYPE ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | FUNC ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState009
      | EOF ->
          let _v_0 = _menhir_action_44 () in
          _menhir_run_147 _menhir_stack _v_0
      | _ ->
          _eRR ()
  
  and _menhir_run_010 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_TYPE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState010 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_030 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FUNC (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState030 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_072 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_DOT as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LEFTPAR ->
          let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState072
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | DOT | EQ | LEFTBRACE | MINUS | MINUSMINUS | PERCENT | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
          let MenhirCell1_DOT (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e, _startpos_e_, _) = _menhir_stack in
          let (_endpos_id_, id) = (_endpos, _v) in
          let _v = _menhir_action_14 e id in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_id_ _startpos_e_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_061 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_ident as 'stack) -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_LEFTPAR (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState061
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState061
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState061
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState061
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState061
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState061
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState061
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState061
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState061
      | RIGHTPAR ->
          let _v = _menhir_action_54 () in
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_052 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos_s_, _startpos_s_, s) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_10 s in
      _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_s_ _startpos_s_ _v _menhir_s _tok
  
  and _menhir_goto_expr_desc : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_d_, _startpos_d_, d) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_08 _endpos_d_ _startpos_d_ d in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_d_ _startpos_d_ _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState109 ->
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState046 ->
          _menhir_run_123 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState099 ->
          _menhir_run_123 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState132 ->
          _menhir_run_123 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_123 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState113 ->
          _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState102 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState053 ->
          _menhir_run_094 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState055 ->
          _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState056 ->
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState058 ->
          _menhir_run_090 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState084 ->
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState082 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState080 ->
          _menhir_run_081 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState078 ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState074 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState069 ->
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState067 ->
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState100 ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState086 ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState061 ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_127 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_FOR as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VERTICALBARVERTICALBAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState127
      | STAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState127
      | SLASH ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState127
      | PLUSPLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState127
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState127
      | MINUSMINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState127
      | LEFTBRACE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState127
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState127
      | COMP _v_0 ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_082 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState127
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_086 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState127
      | AMPERSANDAMPERSAND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState127
      | COLONEQ | EQ ->
          let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_70 x in
          _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v _menhir_s _tok
      | SEMICOLON ->
          let e = _v in
          let _v = _menhir_action_74 e in
          _menhir_goto_simple_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_067 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_VERTICALBARVERTICALBAR (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState067 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_053 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_STAR (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState053 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_054 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos__1_, _startpos__1_) = (_endpos, _startpos) in
      let _v = _menhir_action_11 () in
      _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__1_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_run_055 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_MINUS (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState055 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_056 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_LEFTPAR (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState056 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_057 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos_c_, _startpos_c_, c) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_09 c in
      _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_c_ _startpos_c_ _v _menhir_s _tok
  
  and _menhir_run_058 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_BANG (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState058 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_059 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_AMP (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState059 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_069 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_STAR (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState069 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_074 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_SLASH (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState074 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_124 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_expr -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _endpos__1_ = _endpos in
      let _v = _menhir_action_41 () in
      _menhir_goto_incdec _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__1_ _v _tok
  
  and _menhir_goto_incdec : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, e, _startpos_e_, _) = _menhir_stack in
      let (_endpos_i_, i) = (_endpos, _v) in
      let _v = _menhir_action_78 e i in
      _menhir_goto_simple_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_i_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_goto_simple_stmt_desc : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_d_, _startpos_d_, d) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_75 _endpos_d_ _startpos_d_ d in
      _menhir_goto_simple_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_simple_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState046 ->
          _menhir_run_134 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState099 ->
          _menhir_run_134 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState132 ->
          _menhir_run_134 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState109 ->
          _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_134 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let s = _v in
      let _v = _menhir_action_84 s in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | STRING _v_0 ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState132
          | STAR ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | SEMICOLON ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | RETURN ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | NIL ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | MINUS ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | LEFTPAR ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | LEFTBRACE ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | IF ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | IDENT _v_1 ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState132
          | FOR ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | CST _v_2 ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState132
          | BANG ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | AMP ->
              let _menhir_stack = MenhirCell1_stmt (_menhir_stack, _menhir_s, _v) in
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState132
          | RIGHTBRACE ->
              let s = _v in
              let _v = _menhir_action_80 s in
              _menhir_goto_statements _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | RIGHTBRACE ->
          let s = _v in
          let _v = _menhir_action_79 s in
          _menhir_goto_statements _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_047 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_VAR (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState047 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_099 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | STRING _v ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState099
      | STAR ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | RETURN ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | NIL ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | MINUS ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | LEFTPAR ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | LEFTBRACE ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | IF ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | IDENT _v ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState099
      | FOR ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | CST _v ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState099
      | BANG ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | AMP ->
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) in
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | RIGHTBRACE ->
          let _v = _menhir_action_83 () in
          _menhir_goto_statements _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_100 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState100
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState100
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState100
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState100
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState100
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState100
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState100
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState100
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState100
      | RIGHTBRACE | SEMICOLON ->
          let _v = _menhir_action_54 () in
          _menhir_run_101 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_101 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_RETURN -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_RETURN (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_xs_, xs) = (_endpos, _v) in
      let _v = _menhir_action_89 xs in
      _menhir_goto_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_xs_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_goto_stmt_desc : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_d_, _startpos_d_, d) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_87 _endpos_d_ _startpos_d_ d in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_046 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | STRING _v ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState046
      | STAR ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | RIGHTBRACE ->
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos__2_, _startpos__1_) = (_endpos, _startpos) in
          let _v = _menhir_action_02 _endpos__2_ _startpos__1_ in
          _menhir_goto_block _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__2_ _v _menhir_s _tok
      | RETURN ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | NIL ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | MINUS ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | LEFTPAR ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | LEFTBRACE ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | IF ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | IDENT _v ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState046
      | FOR ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | CST _v ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState046
      | BANG ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | AMP ->
          let _menhir_stack = MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos) in
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState046
      | _ ->
          _eRR ()
  
  and _menhir_goto_block : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState045 ->
          _menhir_run_141 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState046 ->
          _menhir_run_136 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState099 ->
          _menhir_run_136 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState132 ->
          _menhir_run_136 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState109 ->
          _menhir_run_129 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState127 ->
          _menhir_run_128 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState116 ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState105 ->
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState103 ->
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_141 : type  ttv_stack. ((((ttv_stack, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR, _menhir_box_file) _menhir_cell1_loption_parameters_ _menhir_cell0_RIGHTPAR, _menhir_box_file) _menhir_cell1_loption_return_type_ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_loption_return_type_ (_menhir_stack, _, ty) = _menhir_stack in
          let MenhirCell0_RIGHTPAR (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_loption_parameters_ (_menhir_stack, _, pl) = _menhir_stack in
          let MenhirCell0_LEFTPAR (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_ident (_menhir_stack, _, id, _, _) = _menhir_stack in
          let MenhirCell1_FUNC (_menhir_stack, _menhir_s) = _menhir_stack in
          let b = _v in
          let _v = _menhir_action_06 b id pl ty in
          _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | TYPE ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState149
      | FUNC ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState149
      | EOF ->
          let _v_0 = _menhir_action_44 () in
          _menhir_run_150 _menhir_stack _v_0
      | _ ->
          _eRR ()
  
  and _menhir_run_136 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let b = _v in
      let _v = _menhir_action_85 b in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_129 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_FOR -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_FOR (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_b_, b) = (_endpos, _v) in
      let _v = _menhir_action_90 _endpos_b_ _startpos__1_ b in
      _menhir_goto_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_b_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_run_128 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_FOR, _menhir_box_file) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _, e1, _, _) = _menhir_stack in
      let MenhirCell1_FOR (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_b_, b) = (_endpos, _v) in
      let _v = _menhir_action_91 b e1 in
      _menhir_goto_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_b_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_run_117 : type  ttv_stack. (((((ttv_stack, _menhir_box_file) _menhir_cell1_FOR, _menhir_box_file) _menhir_cell1_opt_simple_stmt, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_SEMICOLON, _menhir_box_file) _menhir_cell1_opt_simple_stmt -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_opt_simple_stmt (_menhir_stack, _, s3) = _menhir_stack in
      let MenhirCell1_SEMICOLON (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, e2, _, _) = _menhir_stack in
      let MenhirCell1_opt_simple_stmt (_menhir_stack, _, s1) = _menhir_stack in
      let MenhirCell1_FOR (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_b_, b) = (_endpos, _v) in
      let _v = _menhir_action_92 _endpos_b_ _startpos__1_ b e2 s1 s3 in
      _menhir_goto_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_b_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_run_108 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_IF, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_block -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_block (_menhir_stack, _, s1, _) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, e, _, _) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_s2_, s2) = (_endpos, _v) in
      let _v = _menhir_action_39 e s1 s2 in
      _menhir_goto_if_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_s2_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_goto_if_stmt_desc : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_d_, _startpos_d_, d) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_36 _endpos_d_ _startpos_d_ d in
      _menhir_goto_if_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_d_ _v _menhir_s _tok
  
  and _menhir_goto_if_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState046 ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState099 ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState132 ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState105 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_135 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let s = _v in
      let _v = _menhir_action_86 s in
      _menhir_goto_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_107 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_IF, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_block -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_block (_menhir_stack, _, s1, _) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, e, _, _) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_s2_, s2) = (_endpos, _v) in
      let _v = _menhir_action_38 e s1 s2 in
      _menhir_goto_if_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_s2_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_run_104 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_IF, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _menhir_stack = MenhirCell1_block (_menhir_stack, _menhir_s, _v, _endpos) in
          let _menhir_s = MenhirState105 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LEFTBRACE ->
              _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_102 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | RIGHTBRACE | SEMICOLON ->
          let MenhirCell1_expr (_menhir_stack, _, e, _, _) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_s_, s) = (_endpos, _v) in
          let _v = _menhir_action_37 _endpos_s_ _startpos__1_ e s in
          _menhir_goto_if_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_s_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_102 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState102 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_109 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell1_FOR (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState109
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState109
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState109
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState109
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState109
      | LEFTBRACE ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState109
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState109
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState109
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState109
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState109
      | SEMICOLON ->
          let _v =
            let _endpos__0_ = _endpos in
            _menhir_action_56 _endpos__0_
          in
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState109 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_112 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_FOR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_opt_simple_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _menhir_s = MenhirState113 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STRING _v ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NIL ->
              _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LEFTPAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BANG ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMP ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_statements : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState046 ->
          _menhir_run_139 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState099 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState132 ->
          _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_139 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_LEFTBRACE -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_LEFTBRACE (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos__3_, l) = (_endpos, _v) in
      let _v = _menhir_action_03 _endpos__3_ _startpos__1_ l in
      _menhir_goto_block _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__3_ _v _menhir_s _tok
  
  and _menhir_run_137 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_SEMICOLON -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_SEMICOLON (_menhir_stack, _menhir_s) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_82 l in
      _menhir_goto_statements _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_133 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_stmt -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_stmt (_menhir_stack, _menhir_s, s) = _menhir_stack in
      let l = _v in
      let _v = _menhir_action_81 l s in
      _menhir_goto_statements _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_111 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let s = _v in
      let _v = _menhir_action_57 s in
      _menhir_goto_opt_simple_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_opt_simple_stmt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState115 ->
          _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState109 ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_116 : type  ttv_stack. (((((ttv_stack, _menhir_box_file) _menhir_cell1_FOR, _menhir_box_file) _menhir_cell1_opt_simple_stmt, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_SEMICOLON as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_opt_simple_stmt (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LEFTBRACE ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState116
      | _ ->
          _eRR ()
  
  and _menhir_run_076 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PLUS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState076 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_078 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PERCENT (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState078 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_125 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_expr -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _endpos__1_ = _endpos in
      let _v = _menhir_action_42 () in
      _menhir_goto_incdec _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__1_ _v _tok
  
  and _menhir_run_080 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_MINUS (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState080 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_071 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DOT (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState071 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_082 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_COMP (_menhir_stack, _menhir_s, _v) in
      let _menhir_s = MenhirState082 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_086 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_COMMA (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState086 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_084 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr as 'stack) -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_AMPERSANDAMPERSAND (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState084 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRING _v ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | STAR ->
          _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NIL ->
          _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BANG ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | AMP ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_expr_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState046 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState099 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState132 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState119 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState109 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState086 ->
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState100 ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState061 ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_095 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let (_endpos_el_, _startpos_el_, el) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_29 el in
      _menhir_goto_exprs _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_el_ _startpos_el_ _v _menhir_s _tok
  
  and _menhir_goto_exprs : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState121 ->
          _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState119 ->
          _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState046 ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState099 ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState132 ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState109 ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState115 ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState051 ->
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_122 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_exprs -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_exprs (_menhir_stack, _menhir_s, lvl, _startpos_lvl_, _) = _menhir_stack in
      let (_endpos_el_, el) = (_endpos, _v) in
      let _v = _menhir_action_77 el lvl in
      _menhir_goto_simple_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_el_ _startpos_lvl_ _v _menhir_s _tok
  
  and _menhir_run_120 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_exprs -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_exprs (_menhir_stack, _menhir_s, lvl, _startpos_lvl_, _) = _menhir_stack in
      let (_endpos_el_, el) = (_endpos, _v) in
      let _v = _menhir_action_76 el lvl in
      _menhir_goto_simple_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_el_ _startpos_lvl_ _v _menhir_s _tok
  
  and _menhir_run_118 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exprs (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _menhir_s = MenhirState119 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STRING _v ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NIL ->
              _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LEFTPAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BANG ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMP ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | COLONEQ ->
          let _menhir_s = MenhirState121 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STRING _v ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NIL ->
              _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LEFTPAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BANG ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMP ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_096 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_VAR, _menhir_box_file) _menhir_cell1_separated_nonempty_list_COMMA_ident_, _menhir_box_file) _menhir_cell1_option_type_expr_ -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let (_endpos_el_, el) = (_endpos, _v) in
      let _v = _menhir_action_43 el in
      let _endpos = _endpos_el_ in
      let (_endpos_x_, x) = (_endpos, _v) in
      let _v = _menhir_action_49 x in
      _menhir_goto_loption_init_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _v _tok
  
  and _menhir_goto_loption_init_ : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_VAR, _menhir_box_file) _menhir_cell1_separated_nonempty_list_COMMA_ident_, _menhir_box_file) _menhir_cell1_option_type_expr_ -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_option_type_expr_ (_menhir_stack, _, ty) = _menhir_stack in
      let MenhirCell1_separated_nonempty_list_COMMA_ident_ (_menhir_stack, _, ids) = _menhir_stack in
      let MenhirCell1_VAR (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_i_, i) = (_endpos, _v) in
      let _v = _menhir_action_88 i ids ty in
      _menhir_goto_stmt_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_i_ _startpos__1_ _v _menhir_s _tok
  
  and _menhir_run_087 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_COMMA -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_COMMA (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _menhir_s, x, _startpos_x_, _) = _menhir_stack in
      let (_endpos_xs_, xs) = (_endpos, _v) in
      let _v = _menhir_action_71 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_xs_ _startpos_x_ _v _menhir_s _tok
  
  and _menhir_run_062 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      let (_endpos_x_, x) = (_endpos, _v) in
      let _v = _menhir_action_55 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _v _menhir_s _tok
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState100 ->
          _menhir_run_101 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState061 ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_063 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_ident, _menhir_box_file) _menhir_cell1_LEFTPAR -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RIGHTPAR ->
          let _endpos_0 = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LEFTPAR (_menhir_stack, _menhir_s, _) = _menhir_stack in
          let (xs, _endpos__3_) = (_v, _endpos_0) in
          let _v = _menhir_action_01 xs in
          _menhir_goto_arguments _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__3_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_arguments : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_ident as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState060 ->
          _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState072 ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_088 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_ident -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_ident (_menhir_stack, _menhir_s, id, _startpos_id_, _) = _menhir_stack in
      let (_endpos_el_, el) = (_endpos, _v) in
      let _v = _menhir_action_15 el id in
      _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_el_ _startpos_id_ _v _menhir_s _tok
  
  and _menhir_run_073 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_DOT, _menhir_box_file) _menhir_cell1_ident -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_ident (_menhir_stack, _, id, _, _) = _menhir_stack in
      let MenhirCell1_DOT (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _menhir_s, e, _startpos_e_, _) = _menhir_stack in
      let (_endpos_el_, el) = (_endpos, _v) in
      let _v = _menhir_action_16 e el id in
      _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_el_ _startpos_e_ _v _menhir_s _tok
  
  and _menhir_run_123 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VERTICALBARVERTICALBAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState123
      | STAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState123
      | SLASH ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState123
      | PLUSPLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState123
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState123
      | MINUSMINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState123
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState123
      | COMP _v_0 ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_082 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState123
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_086 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState123
      | AMPERSANDAMPERSAND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState123
      | COLONEQ | EQ ->
          let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_70 x in
          _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v _menhir_s _tok
      | LEFTBRACE | RIGHTBRACE | SEMICOLON ->
          let e = _v in
          let _v = _menhir_action_74 e in
          _menhir_goto_simple_stmt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_114 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_FOR, _menhir_box_file) _menhir_cell1_opt_simple_stmt as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | VERTICALBARVERTICALBAR ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState114
      | STAR ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState114
      | SLASH ->
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState114
      | SEMICOLON ->
          let _endpos_0 = _menhir_lexbuf.Lexing.lex_curr_p in
          let _menhir_stack = MenhirCell1_SEMICOLON (_menhir_stack, MenhirState114) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STRING _v_1 ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState115
          | STAR ->
              _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState115
          | NIL ->
              _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState115
          | MINUS ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState115
          | LEFTPAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState115
          | IDENT _v_2 ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState115
          | CST _v_3 ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState115
          | BANG ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState115
          | AMP ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState115
          | LEFTBRACE ->
              let _v_4 =
                let _endpos__0_ = _endpos_0 in
                _menhir_action_56 _endpos__0_
              in
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState115 _tok
          | _ ->
              _eRR ())
      | PLUS ->
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState114
      | PERCENT ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState114
      | MINUS ->
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState114
      | DOT ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState114
      | COMP _v_5 ->
          _menhir_run_082 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState114
      | AMPERSANDAMPERSAND ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState114
      | _ ->
          _eRR ()
  
  and _menhir_run_103 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | VERTICALBARVERTICALBAR ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState103
      | STAR ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState103
      | SLASH ->
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState103
      | PLUS ->
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState103
      | PERCENT ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState103
      | MINUS ->
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState103
      | LEFTBRACE ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState103
      | DOT ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState103
      | COMP _v_0 ->
          _menhir_run_082 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState103
      | AMPERSANDAMPERSAND ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState103
      | _ ->
          _eRR ()
  
  and _menhir_run_094 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_STAR as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState094
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | EQ | LEFTBRACE | MINUS | MINUSMINUS | PERCENT | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
          let MenhirCell1_STAR (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e1_, e1) = (_endpos, _v) in
          let _v = _menhir_action_28 e1 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e1_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_093 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_MINUS as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState093
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | EQ | LEFTBRACE | MINUS | MINUSMINUS | PERCENT | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
          let MenhirCell1_MINUS (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e1_, e1) = (_endpos, _v) in
          let _v = _menhir_action_26 e1 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e1_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_091 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_LEFTPAR as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VERTICALBARVERTICALBAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
      | STAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
      | SLASH ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
      | RIGHTPAR ->
          let _endpos_0 = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LEFTPAR (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (e, _endpos__3_) = (_v, _endpos_0) in
          let _v = _menhir_action_12 e in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__3_ _startpos__1_ _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
      | COMP _v_1 ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_082 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState091
      | AMPERSANDAMPERSAND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState091
      | _ ->
          _eRR ()
  
  and _menhir_run_090 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_BANG as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState090
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | EQ | LEFTBRACE | MINUS | MINUSMINUS | PERCENT | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
          let MenhirCell1_BANG (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e1_, e1) = (_endpos, _v) in
          let _v = _menhir_action_25 e1 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e1_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_089 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_AMP as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState089
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | EQ | LEFTBRACE | MINUS | MINUSMINUS | PERCENT | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
          let MenhirCell1_AMP (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_e1_, e1) = (_endpos, _v) in
          let _v = _menhir_action_27 e1 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e1_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_085 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_AMPERSANDAMPERSAND as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState085
      | SLASH ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState085
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState085
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState085
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState085
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState085
      | COMP _v_0 ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_082 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState085
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | EQ | LEFTBRACE | MINUSMINUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
          let MenhirCell1_AMPERSANDAMPERSAND (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_23 e1 e2 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_083 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_COMP as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
      | SLASH ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState083
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | EQ | LEFTBRACE | MINUSMINUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
          let MenhirCell1_COMP (_menhir_stack, _, c) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_22 c e1 e2 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_081 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_MINUS as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState081
      | SLASH ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState081
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState081
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState081
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | EQ | LEFTBRACE | MINUS | MINUSMINUS | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
          let MenhirCell1_MINUS (_menhir_stack, _, _) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_18 e1 e2 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_079 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_PERCENT as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState079
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | EQ | LEFTBRACE | MINUS | MINUSMINUS | PERCENT | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
          let MenhirCell1_PERCENT (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_21 e1 e2 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_077 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_PLUS as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState077
      | SLASH ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState077
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState077
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState077
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | EQ | LEFTBRACE | MINUS | MINUSMINUS | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
          let MenhirCell1_PLUS (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_17 e1 e2 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_075 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_SLASH as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState075
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | EQ | LEFTBRACE | MINUS | MINUSMINUS | PERCENT | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
          let MenhirCell1_SLASH (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_20 e1 e2 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_070 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_STAR as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState070
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | EQ | LEFTBRACE | MINUS | MINUSMINUS | PERCENT | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
          let MenhirCell1_STAR (_menhir_stack, _, _) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_19 e1 e2 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_068 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_expr, _menhir_box_file) _menhir_cell1_VERTICALBARVERTICALBAR as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState068
      | SLASH ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState068
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState068
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState068
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState068
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState068
      | COMP _v_0 ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_082 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState068
      | AMPERSANDAMPERSAND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState068
      | COLONEQ | COMMA | EQ | LEFTBRACE | MINUSMINUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | VERTICALBARVERTICALBAR ->
          let MenhirCell1_VERTICALBARVERTICALBAR (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1, _startpos_e1_, _) = _menhir_stack in
          let (_endpos_e2_, e2) = (_endpos, _v) in
          let _v = _menhir_action_24 e1 e2 in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_e2_ _startpos_e1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_066 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VERTICALBARVERTICALBAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
      | STAR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
      | SLASH ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_074 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
      | PERCENT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
      | COMP _v_0 ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_082 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState066
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_086 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
      | AMPERSANDAMPERSAND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
      | COLONEQ | EQ | LEFTBRACE | RIGHTBRACE | RIGHTPAR | SEMICOLON ->
          let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_70 x in
          _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_060 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LEFTPAR ->
          let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState060
      | AMPERSANDAMPERSAND | COLONEQ | COMMA | COMP _ | DOT | EQ | LEFTBRACE | MINUS | MINUSMINUS | PERCENT | PLUS | PLUSPLUS | RIGHTBRACE | RIGHTPAR | SEMICOLON | SLASH | STAR | VERTICALBARVERTICALBAR ->
          let (_endpos_id_, _startpos_id_, id) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_13 id in
          _menhir_goto_expr_desc _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_id_ _startpos_id_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_031 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_FUNC as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | LEFTPAR ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell0_LEFTPAR (_menhir_stack, _startpos) in
          let _menhir_s = MenhirState032 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | RIGHTPAR ->
              let _v = _menhir_action_50 () in
              _menhir_goto_loption_parameters_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_loption_parameters_ : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_loption_parameters_ (_menhir_stack, _menhir_s, _v) in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell0_RIGHTPAR (_menhir_stack, _endpos) in
      let _menhir_s = MenhirState035 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LEFTPAR ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _menhir_stack = MenhirCell1_LEFTPAR (_menhir_stack, _menhir_s, _startpos) in
          let _menhir_s = MenhirState036 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STAR ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | LEFTBRACE ->
          let _v = _menhir_action_52 () in
          _menhir_goto_loption_return_type_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_STAR (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState015 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_loption_return_type_ : type  ttv_stack. ((((ttv_stack, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR, _menhir_box_file) _menhir_cell1_loption_parameters_ _menhir_cell0_RIGHTPAR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_loption_return_type_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LEFTBRACE ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState045
      | _ ->
          _eRR ()
  
  and _menhir_run_024 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          let _menhir_s = MenhirState025 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | EQ | IDENT _ | RIGHTBRACE | SEMICOLON | STAR ->
          let x = _v in
          let _v = _menhir_action_72 x in
          _menhir_goto_separated_nonempty_list_COMMA_ident_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_ident_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState047 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState025 ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState144 ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState032 ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState023 ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_048 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_VAR as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_separated_nonempty_list_COMMA_ident_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState048
      | IDENT _v_0 ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState048
      | EQ | RIGHTBRACE | SEMICOLON ->
          let _menhir_s = MenhirState048 in
          let _v = _menhir_action_62 () in
          _menhir_goto_option_type_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_option_type_expr_ : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_VAR, _menhir_box_file) _menhir_cell1_separated_nonempty_list_COMMA_ident_ as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_option_type_expr_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _menhir_s = MenhirState051 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STRING _v ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | STAR ->
              _menhir_run_053 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NIL ->
              _menhir_run_054 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LEFTPAR ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BANG ->
              _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | AMP ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | RIGHTBRACE | SEMICOLON ->
          let _v = _menhir_action_48 () in
          _menhir_goto_loption_init_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_026 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_ident -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_ident (_menhir_stack, _menhir_s, x, _, _) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_73 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_ident_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
  
  and _menhir_run_014 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_separated_nonempty_list_COMMA_ident_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState014
      | IDENT _v_0 ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState014
      | _ ->
          _eRR ()
  
  and _menhir_run_017 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      let id = _v in
      let _v = _menhir_action_93 id in
      _menhir_goto_type_expr _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
  
  and _menhir_goto_type_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState048 ->
          _menhir_run_049 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState035 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState038 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState036 ->
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState014 ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState015 ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_049 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_VAR, _menhir_box_file) _menhir_cell1_separated_nonempty_list_COMMA_ident_ as 'stack) -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      let x = _v in
      let _v = _menhir_action_63 x in
      _menhir_goto_option_type_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
  
  and _menhir_run_043 : type  ttv_stack. ((((ttv_stack, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR, _menhir_box_file) _menhir_cell1_loption_parameters_ _menhir_cell0_RIGHTPAR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let ty = _v in
      let _v = _menhir_action_66 ty in
      _menhir_goto_return_type _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_return_type : type  ttv_stack. ((((ttv_stack, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR, _menhir_box_file) _menhir_cell1_loption_parameters_ _menhir_cell0_RIGHTPAR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let x = _v in
      let _v = _menhir_action_53 x in
      _menhir_goto_loption_return_type_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_037 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_type_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STAR ->
              let _menhir_stack = MenhirCell1_COMMA (_menhir_stack, MenhirState037) in
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState038
          | IDENT _v_0 ->
              let _menhir_stack = MenhirCell1_COMMA (_menhir_stack, MenhirState037) in
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState038
          | RIGHTPAR ->
              let _ =
                let x = () in
                _menhir_action_59 x
              in
              _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer
          | _ ->
              _eRR ())
      | RIGHTPAR ->
          let _ = _menhir_action_58 () in
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_040 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_type_expr -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let MenhirCell1_type_expr (_menhir_stack, _menhir_s, ty) = _menhir_stack in
      let _v = _menhir_action_68 ty in
      _menhir_goto_return_types _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_return_types : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState036 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState038 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_041 : type  ttv_stack. ((((ttv_stack, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR, _menhir_box_file) _menhir_cell1_loption_parameters_ _menhir_cell0_RIGHTPAR, _menhir_box_file) _menhir_cell1_LEFTPAR -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_LEFTPAR (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let tyl = _v in
      let _v = _menhir_action_67 tyl in
      _menhir_goto_return_type _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_039 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_type_expr, _menhir_box_file) _menhir_cell1_COMMA -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_COMMA (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_type_expr (_menhir_stack, _menhir_s, ty) = _menhir_stack in
      let tyl = _v in
      let _v = _menhir_action_69 ty tyl in
      _menhir_goto_return_types _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_018 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_separated_nonempty_list_COMMA_ident_ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_separated_nonempty_list_COMMA_ident_ (_menhir_stack, _menhir_s, ids) = _menhir_stack in
      let ty = _v in
      let _v = _menhir_action_35 ids ty in
      _menhir_goto_ids_and_type _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_ids_and_type : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState144 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState032 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState023 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState013 ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_143 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ids_and_type (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v_0 ->
              let _menhir_stack = MenhirCell1_COMMA (_menhir_stack, MenhirState143) in
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState144
          | RIGHTPAR ->
              let _ =
                let x = () in
                _menhir_action_59 x
              in
              _menhir_run_146 _menhir_stack _menhir_lexbuf _menhir_lexer
          | _ ->
              _eRR ())
      | RIGHTPAR ->
          let _ = _menhir_action_58 () in
          _menhir_run_146 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_146 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_ids_and_type -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let MenhirCell1_ids_and_type (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let _v = _menhir_action_64 x in
      _menhir_goto_parameters _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_parameters : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState144 ->
          _menhir_run_145 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState032 ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_145 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_ids_and_type, _menhir_box_file) _menhir_cell1_COMMA -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_COMMA (_menhir_stack, _) = _menhir_stack in
      let MenhirCell1_ids_and_type (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xl = _v in
      let _v = _menhir_action_65 x xl in
      _menhir_goto_parameters _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_033 : type  ttv_stack. (((ttv_stack, _menhir_box_file) _menhir_cell1_FUNC, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTPAR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_51 x in
      _menhir_goto_loption_parameters_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_022 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ids_and_type (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _menhir_s = MenhirState023 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | RIGHTBRACE ->
              let x = () in
              let _ = _menhir_action_61 x in
              _menhir_goto_option_SEMICOLON_ _menhir_stack _menhir_lexbuf _menhir_lexer
          | _ ->
              _eRR ())
      | RIGHTBRACE ->
          let _ = _menhir_action_60 () in
          _menhir_goto_option_SEMICOLON_ _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_SEMICOLON_ : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_ids_and_type -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let MenhirCell1_ids_and_type (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let _v = _menhir_action_30 x in
      _menhir_goto_fields _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_fields : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState013 ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState023 ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_029 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_TYPE, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTBRACE -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let x = _v in
      let _v = _menhir_action_47 x in
      _menhir_goto_loption_fields_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
  
  and _menhir_goto_loption_fields_ : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_TYPE, _menhir_box_file) _menhir_cell1_ident _menhir_cell0_LEFTBRACE -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SEMICOLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_LEFTBRACE (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_ident (_menhir_stack, _, id, _, _) = _menhir_stack in
          let MenhirCell1_TYPE (_menhir_stack, _menhir_s) = _menhir_stack in
          let fl = _v in
          let _v = _menhir_action_07 fl id in
          _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_027 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_ids_and_type -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_ids_and_type (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xl = _v in
      let _v = _menhir_action_31 x xl in
      _menhir_goto_fields _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_016 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_STAR -> _ -> _ -> _ -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_STAR (_menhir_stack, _menhir_s, _) = _menhir_stack in
      let ty = _v in
      let _v = _menhir_action_94 ty in
      _menhir_goto_type_expr _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
  
  and _menhir_run_011 : type  ttv_stack. ((ttv_stack, _menhir_box_file) _menhir_cell1_TYPE as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_ident (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | STRUCT ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LEFTBRACE ->
              let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
              let _menhir_stack = MenhirCell0_LEFTBRACE (_menhir_stack, _startpos) in
              let _menhir_s = MenhirState013 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | RIGHTBRACE ->
                  let _v = _menhir_action_46 () in
                  _menhir_goto_loption_fields_ _menhir_stack _menhir_lexbuf _menhir_lexer _v
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  let _menhir_run_000 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | PACKAGE ->
          let _menhir_s = MenhirState001 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
end

let file =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_file v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
