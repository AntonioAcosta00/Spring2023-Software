#include <stdio.h>

#include "ast.h"
#include "id_attrs.h"
#include "lexer.h"
#include "parserInternal.h"
#include "token.h"
#include "utilities.h"


static token tok;

void parser_open(const char *filename) {
  lexer_open(filename);
  tok = lexer_next();
}

void parser_close() { lexer_close(); }

void advance() {
  if (!lexer_done()) {
    tok = lexer_next();
  }
}

static void add_AST_to_end(AST_list *head, AST_list *last, AST_list lst) {
  if (ast_list_is_empty(*head)) {
    *head = lst;
    *last = ast_list_last_elem(lst);
  } else {
    ast_list_splice(*last, lst);
    *last = ast_list_last_elem(lst);
  }
}

void eat(token_type tt) {
  if (tok.typ == tt) {
    advance();
  } else {
    token_type expected[1] = {tt};
    parse_error_unexpected(expected, 1, tok);
  }
}

// <assignment> ::= <ident> := <expr>
static AST *parse_assign_stmt() {
  token idtok = tok;
  eat(identsym);
  eat(becomessym);
  AST *exp = parse_expr();
  return ast_assign_stmt(idtok, idtok.text, exp);
}

// ⟨program⟩ ::= ⟨block⟩ .
// This is the lab program they had us do for parseProgram
AST *parse_program() {
  AST *programast = parse_block();
  eat(periodsym);
  eat(eofsym);
  return programast;
}

// ⟨block⟩ ::= ⟨const-decls⟩ ⟨var-decls⟩ ⟨stmt⟩
static AST *parse_block() {
  AST_list const_decls = parse_const_decls();
  AST_list var_decls = parse_var_decls();
  AST *stmt = parse_stmt();

  file_location floc;

  if (!ast_list_is_empty(const_decls)) {
    if (ast_list_first(const_decls)->type_tag == const_decl_ast) {
      floc = ast_list_first(const_decls)->file_loc;
    } else {
      bail_with_error("Bad AST for const declarations");
    }
  } else if (!ast_list_is_empty(var_decls)) {
    if (ast_list_first(var_decls)->type_tag == var_decl_ast) {
      floc = ast_list_first(var_decls)->file_loc;
    } else {
      bail_with_error("Bad AST for var declarations");
    }
  } else {
    floc = stmt->file_loc;
  }

  return ast_program(floc.filename, floc.line, floc.column, const_decls,
                     var_decls, stmt);
}

// I think I got parse_const_decls and parse_var_decls done
// Sorry I had to rewrite it so I could understand how it works

// Parses a list of const-defs from multiple lines of const declarations
// ⟨const-decls⟩ ::= { ⟨const-decl⟩ }
static AST_list parse_const_decls() {
  AST_list ret = ast_list_empty_list();
  AST_list last = ast_list_empty_list();

  // Each iteration of this loop will parse a const-decl
  while (tok.typ == constsym) {
    // Parse the first declaration
    // Ex. const var1 = 1
    eat(constsym);
    AST *first_declaration = parse_const_def();
    add_AST_to_end(&ret, &last, ast_list_singleton(first_declaration));

    // Parse any additional declarations from the same line
    // Ex. ..., var2 = 2, var3 = 3
    while (tok.typ == commasym) {
      eat(commasym);
      AST *additional_declaration = parse_const_def();
      add_AST_to_end(&ret, &last, ast_list_singleton(additional_declaration));
    }

    eat(semisym);
  }

  return ret;
}

// <const-def> ::= <ident> = <number>
static AST *parse_const_def() {
  token ident = tok;
  eat(identsym);
  eat(eqsym);
  short int numval = tok.value;
  eat(numbersym);
  AST *ret = ast_const_def(ident, ident.text, numval);
  return ret;
}

// ⟨var-decls⟩ ::= { ⟨var-decl⟩ }
static AST_list parse_var_decls() {
  AST_list ret = ast_list_empty_list();
  AST_list last = ast_list_empty_list();

  // Each iteration of this loop will parse a var-decl
  while (tok.typ == varsym) {
    // Parse the first variable declaration
    // Ex. var var1
    eat(varsym);
    AST *first_var_decl = parse_ident_as_var_decl();
    add_AST_to_end(&ret, &last, ast_list_singleton(first_var_decl));

    // Parse any additional variable declarations from the same line
    // Ex. ..., var2, var3
    while (tok.typ == commasym) {
      eat(commasym);
      AST *additional_var_decl = parse_ident_as_var_decl();
      add_AST_to_end(&ret, &last, ast_list_singleton(additional_var_decl));
    }

    eat(semisym);
  }

  return ret;
}

// everything from below here should be done

AST *parse_ident_as_var_decl() {
  token ident = tok;
  eat(identsym);
  return ast_var_decl(ident, ident.text);
}

// <idents> ::= <ident> { <comma-ident> }
static AST_list parse_idents() {
  token idtok = tok;
  eat(identsym);

  AST_list ret = ast_list_singleton(ast_var_decl(idtok, idtok.text));
  AST_list last = ret;

  while (tok.typ == commasym) {
    eat(commasym);
    token idtok = tok;
    eat(identsym);
    AST *vd = ast_var_decl(idtok, idtok.text);
    add_AST_to_end(&ret, &last, ast_list_singleton(vd));
  }

  return ret;
}

/**
⟨stmt⟩ ::= ⟨ident⟩ := ⟨expr⟩
  | begin ⟨stmt⟩ { ⟨semi-stmt⟩ } end
  | if ⟨condition⟩ then ⟨stmt⟩ else ⟨stmt⟩
  | while ⟨condition⟩ do ⟨stmt⟩
  | read ⟨ident⟩
  | write ⟨expr⟩
  | skip
**/
static AST *parse_stmt() {
  AST *ret = NULL;

  switch (tok.typ) {
  case identsym:
    ret = parse_assign_stmt();
    break;
  case beginsym:
    ret = parse_begin_stmt();
    break;
  case ifsym:
    ret = parse_if_stmt();
    break;
  case whilesym:
    ret = parse_while_stmt();
    break;
  case readsym:
    ret = parse_read_stmt();
    break;
  case writesym:
    ret = parse_write_stmt();
    break;
  case skipsym:
    ret = parse_skip_stmt();
    break;
  default:;
    token_type expected[7] = {identsym, beginsym, ifsym,  whilesym,
                              readsym,  writesym, skipsym};
    parse_error_unexpected(expected, 7, tok);
  }

  return ret;
}

// ⟨semi-stmt⟩ ::= ; ⟨stmt⟩
static AST *parse_semi_stmt() {
  eat(semisym);
  return parse_stmt();
}

// begin ⟨stmt⟩ { ⟨semi-stmt⟩ } end
static AST *parse_begin_stmt() {
  token t = tok;
  eat(beginsym);

  AST_list stmts = ast_list_singleton(parse_stmt());
  AST_list last = stmts;

  while (tok.typ == semisym) {
    AST *stmt = parse_semi_stmt();
    add_AST_to_end(&stmts, &last, ast_list_singleton(stmt));
  }

  eat(endsym);
  AST *ret = ast_begin_stmt(t, stmts);

  return ret;
}

//  | while ⟨condition⟩ do ⟨stmt⟩
static AST *parse_while_stmt() {
  token t = tok;
  eat(whilesym);
  AST *condition = parse_condition();
  eat(dosym);
  AST *stmt = parse_stmt();
  return ast_while_stmt(t, condition, stmt);
}

//  | if ⟨condition⟩ then ⟨stmt⟩ else ⟨stmt⟩
static AST *parse_if_stmt() {
  token t = tok;
  eat(ifsym);

  AST *condition = parse_condition();
  eat(thensym);

  AST *s1 = parse_stmt();
  eat(elsesym);

  AST *s2 = parse_stmt();
  return ast_if_stmt(t, condition, s1, s2);
}

//  | read ⟨ident⟩
static AST *parse_read_stmt() {
  token t = tok;
  eat(readsym);
  const char *name = tok.text;
  eat(identsym);
  return ast_read_stmt(t, name);
}

//   | write ⟨expr⟩
static AST *parse_write_stmt() {
  token t = tok;
  eat(writesym);
  AST *exp = parse_expr();
  return ast_write_stmt(t, exp);
}

//  | skip
static AST *parse_skip_stmt() {
  token t = tok;
  eat(skipsym);
  return ast_skip_stmt(t);
}

static AST *parse_odd() {
  token t = tok;
  eat(oddsym);
  AST *exp = parse_expr();
  return ast_odd_cond(t, exp);
}

static AST *parse_expr_rel_op() {
  token t = tok;
  AST *e1 = parse_expr();
  rel_op r = parse_rel_op();
  AST *e2 = parse_expr();
  AST *ret = ast_bin_cond(tok, e1, r, e2);
  ret->file_loc = token2file_loc(t);
  return ret;
}

/**
⟨condition⟩ ::= odd ⟨expr⟩
  | ⟨expr⟩ ⟨rel-op⟩ ⟨expr⟩
**/
static AST *parse_condition() {
  AST *ret;
  switch (tok.typ) {
  case oddsym:
    ret = parse_odd();
    break;
  default:
    ret = parse_expr_rel_op();
    break;
  }
  return ret;
}

// ⟨rel-op⟩ ::= = | <> | < | <= | > | >=
// need this
static rel_op parse_rel_op() {
  switch (tok.typ) {
  case eqsym:
    eat(eqsym);
    return eqop;
    break;
  case neqsym:
    eat(neqsym);
    return neqop;
    break;
  case lessym:
    eat(lessym);
    return ltop;
    break;
  case leqsym:
    eat(leqsym);
    return leqop;
    break;
  case gtrsym:
    eat(gtrsym);
    return gtop;
    break;
  case geqsym:
    eat(geqsym);
    return geqop;
    break;
  default:;
    token_type expected[6] = {eqsym, neqsym, lessym, leqsym, gtrsym, geqsym};
    parse_error_unexpected(expected, 6, tok);
    break;
  }

  return (rel_op)0;
}

// ⟨expr⟩ ::= ⟨term⟩ { ⟨add-sub-term⟩ }
static AST *parse_expr() {
  token fst = tok;

  AST *trm = parse_term();
  AST *exp = trm;

  while (tok.typ == plussym || tok.typ == minussym) {
    AST *rght = parse_add_sub_term();
    exp = ast_bin_expr(fst, exp, rght->data.op_expr.arith_op,
                       rght->data.op_expr.exp);
  }

  return exp;
}

// ⟨add-sub-term⟩ ::= ⟨add-sub⟩ ⟨term⟩
static AST *parse_add_sub_term() {
  token opt = tok;
  switch (tok.typ) {
  case plussym:
    eat(plussym);
    AST *exp = parse_term();
    return ast_op_expr(opt, addop, exp);
    break;
  case minussym:
    eat(minussym);
    AST *e = parse_term();
    return ast_op_expr(opt, subop, e);
    break;
  default:;
    token_type expected[2] = {plussym, minussym};
    parse_error_unexpected(expected, 2, tok);
    break;
  }
  return (AST *)NULL;
}

// ⟨term⟩ ::= ⟨factor⟩ { ⟨mult-div-factor⟩ }
static AST *parse_term() {
  token fst = tok;
  AST *fac = parse_factor();
  AST *exp = fac;

  while (tok.typ == multsym || tok.typ == divsym) {
    AST *rght = parse_mult_div_factor();
    exp = ast_bin_expr(fst, exp, rght->data.op_expr.arith_op,
                       rght->data.op_expr.exp);
  }

  return exp;
}

// ⟨mult-div-factor⟩ ::= ⟨mult-div⟩ ⟨factor⟩
static AST *parse_mult_div_factor() {
  token opt = tok;
  switch (tok.typ) {
  case multsym:
    eat(multsym);
    AST *exp = parse_factor();
    return ast_op_expr(opt, multop, exp);
    break;
  case divsym:
    eat(divsym);
    AST *e = parse_factor();
    return ast_op_expr(opt, divop, e);
    break;
  default:;
    token_type expected[2] = {multsym, divsym};
    parse_error_unexpected(expected, 2, tok);
    break;
  }

  return (AST *)NULL;
}

static AST *parse_paren_expr() {
  token lpt = tok;
  eat(lparensym);
  AST *ret = parse_expr();
  eat(rparensym);
  ret->file_loc = token2file_loc(lpt);
  return ret;
}

// ⟨factor⟩ ::= ⟨ident⟩ | ⟨sign⟩ ⟨number⟩ | ( ⟨expr⟩ )
static AST *parse_factor() {
  switch (tok.typ) {
  case identsym: {
    token identTok = tok;
    eat(identsym);
    return ast_ident(identTok, identTok.text);
    break;
  }
  case lparensym:
    return parse_paren_expr();
    break;
  case plussym:
    return parse_number_expr();
    break;
  case minussym:
    return parse_number_expr();
    break;
  case numbersym:
    return parse_number_expr();
    break;
  default:;
    token_type expected[5] = {identsym, lparensym, plussym, minussym,
                              numbersym};
    parse_error_unexpected(expected, 5, tok);
    break;
  }
  // The following should never execute
  return (AST *)NULL;
}

// ⟨sign⟩ ::= ⟨plus⟩ | ⟨minus⟩ | ⟨empty⟩
static AST *parse_number_expr() {
  int neg = 0;
  token t = tok;
  switch (tok.typ) {

  case plussym:
    eat(plussym);
    break;
  case minussym:
    eat(minussym);
    neg = 1;
    break;
  default:
    break;
  }
  token numt = tok;
  eat(numbersym);
  short int val = numt.value;
  if (neg == 1) {
    val = -val;
  }
  return ast_number(numt, val);
}
