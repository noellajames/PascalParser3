%{     /* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 30 Jul 13   */
/* Copyright (c) 2013 Gordon S. Novak Jr. and
   The University of Texas at Austin. */
/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12 */
/*
; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.
; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.
; You should have received a copy of the GNU General Public License
; along with this program; if not, see <http://www.gnu.org/licenses/>.
  */
/* NOTE:   Copy your lexan.l lexical analyzer to this directory.      */
       /* To use:
                     make pars1y              has 1 shift/reduce conflict
                     pars1y                   execute the parser
                     i:=j .
                     ^D                       control-D to end input
                     pars1y                   execute the parser
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.
                     ^D
                     pars1y                   execute the parser
                     if x+y then if y+z then i:=j else k:=2.
                     ^D
           You may copy pars1.y to be parse.y and extend it for your
           assignment.  Then use   make parser   as above.
        */
        /* Yacc reports 1 shift/reduce conflict, due to the ELSE part of
           the IF statement, but Yacc's default resolves it in the right way.*/
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
        /* define the type of the Yacc stack element to be TOKEN */
#define YYSTYPE TOKEN
TOKEN parseresult;
        /* maximum amount of user labels */
#define MAX_USER_LABEL	100

int user_label[MAX_USER_LABEL];
%}

/* Order of tokens corresponds to tokendefs.c; do not change */

%token IDENTIFIER STRING NUMBER   /* token types */

%token PLUS MINUS TIMES DIVIDE    /* Operators */
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA                      /* Delimiters */
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN           /* Lex uses BEGIN */
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH
%left  PLUS MINUS OR
%left  TIMES DIVIDE DIV MOD AND
%right UMINUS UPLUS

%%

  program    :  PROGRAM IDENTIFIER LPAREN id_list RPAREN SEMICOLON lblock DOT   { parseresult = makeprogram($2, $4, $7); }
             ;
  lblock     :  LABEL numlist SEMICOLON cblock     { $$ = $4; }
             |  cblock
             ;
  numlist    :  NUMBER COMMA numlist	            { instlabel($1); }
  	  	     |  NUMBER                              { instlabel($1); }
		     ;
  cblock     :  CONST cdef_list tblock	            { $$ = $3; } 
  	  	  	 |  tblock
  	  	  	 ;
  cdef_list  :  cdef SEMICOLON cdef_list            { /* do nothing */ }
             |  cdef SEMICOLON                      { /* do nothing */ }
             ;
  cdef       :  IDENTIFIER EQ constant              { instconst($1, $3); }
  	  	  	 ;
  tdef       :  IDENTIFIER EQ type                  { insttype($1, $3); }
             ;
  tdef_list  :  tdef SEMICOLON tdef_list            { $$ = cons($1, $3); }
  	  	  	 |  tdef SEMICOLON                      { $$ = $1; }
		     ;
  tblock     :  TYPE tdef_list vblock               { $$ = $3; }
             |  vblock
  	  	     ;
  label      :  NUMBER COLON statement              { $$ = dolabel($1, $2, $3); }
             ;
  statement  :  BEGINBEGIN statement endpart
                                       { $$ = makeprogn($1,cons($2, $3)); }
             |  IF expr THEN statement endif   { $$ = makeif($1, $2, $4, $5); }
             |  FOR assignment TO expr DO statement	{ $$ = makefor(1, $1, $2, $3, $4, $5, $6); }
             |  FOR assignment DOWNTO expr DO statement	{ $$ = makefor(-1, $1, $2, $3, $4, $5, $6);}
             |  WHILE expr DO statement           { $$ = makewhile($1, $2, $3, $4); }
             |  REPEAT statement_list UNTIL expr		{$$ = makerepeat($1, $2, $3, $4); }
             |  assignment
			 |  funcall
			 |  GOTO NUMBER                       { $$ = dogoto($1, $2); }
			 |  label
             ;
  statement_list  :  statement SEMICOLON statement_list			{ $$ = cons($1, $3); }
  	  	  	  	  |  statement 
				  ;
  endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
             |  END                            { $$ = NULL; }
             ;
  endif      :  ELSE statement                 { $$ = $2; }
             |  /* empty */                    { $$ = NULL; }
             ;
  assignment :  IDENTIFIER ASSIGN expr         { $$ = binop($2, findid($1), $3); }
             ;
  id_list    : IDENTIFIER COMMA id_list        { $$ = cons($1, $3); }
             | IDENTIFIER
			 ;
  simple_type : IDENTIFIER
              | LPAREN id_list RPAREN          { $$ = instenum($2); }
              | constant DOTDOT constant       { $$ = instdotdot($1, $2, $3); }
              ;
  simple_type_list : simple_type COMMA simple_type_list        { $$ = cons($1, $3); }
		           | simple_type
		           ;
  type       : simple_type
             | ARRAY LBRACKET simple_type_list RBRACKET OF type		{ $$ = instarray($3, $6); }
             | RECORD field_list END           { $$ = instrec($1, $2); }
             ;
  fields     : id_list COLON type              { $$ = instfields($1, $3); }
             ;
  field_list : fields SEMICOLON field_list     { $$ = nconc($1, $3); }
  	  	     | fields
		     ;
  vdef       : id_list COLON type             { instvars($1, $3); }
             ;
  vdef_list  : vdef SEMICOLON vdef_list            { /* do nothing */ }
             | vdef SEMICOLON                      { /* do nothing */ }
			 ;
  vblock     : VAR vdef_list block            { $$ = $3; }
             | block                          
			 ;
  block      : BEGINBEGIN statement endpart   { $$ = makeprogn($1,cons($2, $3)); }
             ;
  funcall    : IDENTIFIER LPAREN expr_list RPAREN  { $$ = makefuncall($2, $1, $3); }
  	  	  	 ;
  expr_list  : expr COMMA expr_list            { $$ = cons($1, $3); }
             | expr
			 ;
  expr       : expr compare_op simple_expr     { $$ = binop($2, $1, $3); }
             | simple_expr
			 ;
  simple_expr :  simple_expr plus_op term      { $$ = binop($2, $1, $3); }
              |  MINUS term %prec UMINUS       { $$ = unaryop($1, $2); }
              |  PLUS term %prec UPLUS         { $$ = unaryop($1, $2); }
			  |  term 
              ;
  term       :  term times_op factor           { $$ = binop($2, $1, $3); }
             |  factor
             ;
  factor     :  LPAREN expr RPAREN             { $$ = $2; }
             |  unsigned_constant
			 |  funcall
             ;
  plus_op    :  PLUS
  	  	     |  MINUS
			 |  OR
			 ;
  times_op   :  TIMES
  	  	  	 |  DIVIDE
			 |  DIV
			 |  MOD
			 |  AND
			 ;
  compare_op :  EQ 
             |  LT 
			 |  GT 
			 |  NE 
			 |  LE 
			 |  GE 
			 |  IN
			 ;
  unsigned_constant : IDENTIFIER 	{ $$ = findid($1); }
                    | NUMBER 
					| NIL 
					| STRING
					;
  sign       :  PLUS 
  	  	  	 |  MINUS
			 ;
  constant	 :  sign IDENTIFIER		{ $$ = unaryop($1, $2); }
  	  	  	 |  IDENTIFIER
			 |  sign NUMBER			{ $$ = unaryop($1, $2); }
			 |  NUMBER
			 |  STRING
			 ;
%%
/* You should add your own debugging flags below, and add debugging
   printouts to your programs.
   You will want to change DEBUG to turn off printouts once things
   are working.
  */
#define DEBUG       2047            /* set bits here for debugging, 0 = off  */
#define DB_CONS       1             /* bit to trace cons */
#define DB_BINOP      2             /* bit to trace binop */
#define DB_MAKEIF     4             /* bit to trace makeif */
#define DB_MAKEPROGN  8             /* bit to trace makeprogn */
#define DB_PARSERES  16             /* bit to trace parseresult */
#define DB_UNARYOP   32             /* bit to trace unaryop */
#define DB_VAR       64
#define DB_REPEAT    128
#define DB_FIX		 256
#define DB_WHILE     512
#define DB_TYPE      1024
 int labelnumber = 0;  /* sequential counter for internal label numbers */
   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */
TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
  }

int is_arithmetic_operator(TOKEN po) {
	int op = po->whichval;
	if ((op == PLUSOP) || (op == MINUSOP) || (op == TIMESOP) || (op == DIVIDEOP) || (op == DIVOP) || (op == MODOP)) {
		return 1;
	}
	return 0;
}

int basic_data_type(TOKEN tok) {
	if (tok->tokentype == NUMBERTOK || tok->tokentype == IDENTIFIERTOK) {
		return tok->datatype;
	} else if (tok->tokentype == OPERATOR) {
		if (tok->whichval == FIXOP) {
			return INTEGER;
		} else if (tok->whichval == FLOATOP) {
			return REAL;
		} else if (tok->whichval == FUNCALLOP) {
			return tok->operands->datatype;
		} else {
			return basic_data_type(tok->operands);
		}
	}  else if (tok->tokentype == STRINGTOK) {
		return STRINGTYPE;
	}
	printf("ONE - Not an argument to a binary operator");
	dbugprinttok(tok);
	printf("TWO - Not an argument to a binary operator");
	return -1;
}

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { 
	int lhs_data_type = basic_data_type(lhs);
	int rhs_data_type = basic_data_type(rhs);
    if((lhs_data_type == INTEGER) && (rhs_data_type == REAL) && is_arithmetic_operator(op)) {
    	lhs = makefloat(lhs);
   	} else if ((lhs_data_type == REAL) && (rhs_data_type == INTEGER) && is_arithmetic_operator(op)) {
   		rhs = makefloat(rhs);
   	} else if((lhs_data_type == INTEGER) && (rhs_data_type == REAL) && (op->whichval == ASSIGNOP)) {
   		rhs = makefix(rhs);
   	} else if ((lhs_data_type == REAL) && (rhs_data_type == INTEGER) && (op->whichval == ASSIGNOP)) {
   		rhs = makefloat(rhs);
    }
    
	op->operands = lhs;          /* link operands to operator       */
    lhs->link = rhs;             /* link second operand to first    */
    rhs->link = NULL;            /* terminate operand list          */
    
    if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(lhs);
         dbugprinttok(rhs);
       };
    return op;
  }
/* unaryop links a unary operator op to one operand, lhs */
TOKEN unaryop(TOKEN op, TOKEN lhs) {
	op->operands = lhs;          /* link operands to operator       */
	lhs->link = NULL;             /* terminate operand list    */
	if (DEBUG & DB_UNARYOP) { 
		printf("unaryop\n");
	    dbugprinttok(op);
	    dbugprinttok(lhs);
	};
	return op;
}
/* makeop makes a new operator token with operator number opnum.
   Example:  makeop(FLOATOP)  */
TOKEN makeop(int opnum) {
	TOKEN tok = talloc();
	tok->tokentype = OPERATOR;
	tok->whichval = opnum;
	return tok;
}
TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
  {  tok->tokentype = OPERATOR;  /* Make it look like an operator   */
     tok->whichval = IFOP;
     if (elsepart != NULL) elsepart->link = NULL;
     thenpart->link = elsepart;
     exp->link = thenpart;
     tok->operands = exp;
     if (DEBUG & DB_MAKEIF)
        { printf("makeif\n");
          dbugprinttok(tok);
          dbugprinttok(exp);
          dbugprinttok(thenpart);
          dbugprinttok(elsepart);
        };
     return tok;
   }
/* makefuncall makes a FUNCALL operator and links it to the fn and args.
   tok is a (now) unused token that is recycled. */
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
	TOKEN t1 = makeop(FUNCALLOP);
	findid(fn); /* locate the function in the symbol table */
	return binop(t1, fn, args);
}
TOKEN makeprogn(TOKEN tok, TOKEN statements)
  {  tok->tokentype = OPERATOR;
     tok->whichval = PROGNOP;
     tok->operands = statements;
     if (DEBUG & DB_MAKEPROGN)
       { printf("makeprogn\n");
         dbugprinttok(tok);
         dbugprinttok(statements);
       };
     return tok;
   }
/* fillintc smashes tok, making it into an INTEGER constant with value num */
TOKEN fillintc(TOKEN tok, int num) {
	tok->tokentype = NUMBERTOK;
	tok->intval = num;
	tok->datatype = INTEGER;
	return tok;
}
/* makeintc makes a new token with num as its value */
TOKEN makeintc(int num) {
	TOKEN tok = talloc();
	fillintc(tok, num);
	return tok;
}
/* makelabel makes a new label, using labelnumber++ */
TOKEN makelabel() {
	TOKEN label = makeop(LABELOP);
	TOKEN labelnum = makeintc(labelnumber);
	labelnumber++;
	return unaryop(label, labelnum);
}
/* makegoto makes a GOTO operator to go to the specified label.
   The label number is put into a number token. */
TOKEN makegoto(int label) {
	TOKEN goto_tok = makeop(GOTOOP);
	TOKEN labelnum = makeintc(label);
	return unaryop(goto_tok, labelnum);
}
/* copytok makes a new token that is a copy of origtok */
TOKEN copytok(TOKEN origtok) {
	TOKEN tok = talloc();
	memcpy(tok, origtok, sizeof(struct tokn));
	return tok;
}
/* makefor makes structures for a for statement.
   sign is 1 for normal loop, -1 for downto.
   asg is an assignment statement, e.g. (:= i 1)
   endexpr is the end expression
   tok, tokb and tokc are (now) unused tokens that are recycled. */
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement) {
	int cur_labelnumber = labelnumber;
	TOKEN label_tok = makelabel();
	TOKEN goto_tok = makegoto(cur_labelnumber); 
	/* copy assignment operator for use in multiple situations */
	TOKEN assign_var = copytok(asg->operands);
	TOKEN assign_var1 = copytok(asg->operands);
	TOKEN assign_var2 = copytok(asg->operands);
	TOKEN end_check_tok = 0;
	TOKEN tok_increment = 0;
	TOKEN tok_var_incr = 0;
	/* Build the termination condition */
	if (sign == 1) { /* to */
		end_check_tok = makeop(LEOP);
		tok_increment = makeop(PLUSOP);
	} else { /* downto */
		end_check_tok = makeop(GEOP);
		tok_increment = makeop(MINUSOP);
	}
	end_check_tok = binop(end_check_tok, assign_var, endexpr); /* build final termination condition */
	fillintc(tokb, 1);
	binop(tok_increment, assign_var1, tokb);
	tok_var_incr = makeop(ASSIGNOP);
	binop(tok_var_incr, assign_var2, tok_increment); /* building the increment */
	cons(statement, cons(tok_var_incr, goto_tok)); 
	makeprogn(tokc, statement);
	tok = makeif(tok, end_check_tok, tokc, 0); /* Build if condition */
	/* build using cons to create final tree */
	cons(label_tok, tok);
	cons(asg, label_tok);  
	return makeprogn(talloc(), asg);
	
	
}
/* findtype looks up a type name in the symbol table, puts the pointer
   to its type into tok->symtype, returns tok. */
TOKEN findtype(TOKEN tok) {
	SYMBOL sym, typ;
	char error_details[1024];
	sym = searchst(tok->stringval);
	if (sym == 0) {	/* print error if symbol not found */
		sprintf(error_details, "Type %s not found.\n", tok->stringval);
		yyerror(error_details);
		return tok;
	}
	tok->symentry = sym;	
	tok->symtype = sym;
	return tok;
}
/* instvars will install variables in symbol table.
   typetok is a token containing symbol table pointer for type. */
void  instvars(TOKEN idlist, TOKEN typetok) {
	int symbol_size = 0;
	SYMBOL sym;
	TOKEN tok = idlist;
	if (DEBUG & DB_VAR) {
		printf("initializing vars\n");
		dbugprinttok(typetok);
		dbugprinttok(idlist);
	}
	if (typetok->symtype == 0) {
		findtype(typetok); /* find type */
	}
	
	symbol_size = alignsize (typetok->symtype); /* find the size of type */
	while (tok != 0) {
		sym = insertsym(tok->stringval);
		/* Set up symbol as variable and initialize with block/symbol table info */	
		sym->kind = VARSYM;
		sym->datatype = typetok->symtype;
		sym->size = typetok->symtype->size;
		sym->offset = wordaddress(blockoffs[blocknumber], symbol_size);
		sym->blocklevel = blocknumber;
	    sym->datatype = typetok->symtype;
		sym->basicdt = typetok->symtype->basicdt;
		blockoffs[blocknumber] = sym->size + sym->offset;
		tok = tok->link;
	}
	
}
/* makeprogram makes the tree structures for the top-level program */
TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) {
	TOKEN tok_program = makeop(PROGRAMOP);
	TOKEN tok;
	tok_program->operands = name;
	tok = makeprogn(talloc(), args);
	name->link = tok;
	tok->link = statements;
	return tok_program;
}
/* findid finds an identifier in the symbol table, sets up symbol table
   pointers, changes a constant to its number equivalent */
TOKEN findid(TOKEN tok) {
	SYMBOL sym, typ;
	char error_details[1024];
	sym = searchst(tok->stringval);
	if (sym == 0) { /* return error if ID not found */
		sprintf(error_details, "Identifier %s not found.\n", tok->stringval);
		yyerror(error_details);
		return tok;
	}
	if (sym->kind == CONSTSYM) {
		if (sym->basicdt == INTEGER) {
			tok->tokentype = NUMBERTOK;
			tok->datatype = INTEGER;
			tok->intval = sym->constval.intnum;
		} else if (sym->basicdt == REAL) {
			tok->tokentype = NUMBERTOK;
			tok->datatype = REAL;
			tok->realval = sym->constval.realnum;
		} else if (sym->basicdt == STRINGTYPE) {
			tok->tokentype = STRINGTOK;
			tok->datatype = STRINGTYPE;
			strcpy(tok->stringval, sym->constval.stringconst);
		} else {
			yyerror("Invalid Const ID");
		}
		/* tok->symtype = sym->datatype; */
	} else { /* assuming it to be a variable for now */
		/* fill up token with symbol table entry */
		tok->symentry = sym;
		typ = sym->datatype;
		tok->symtype = typ;
		if (sym->kind == FUNCTIONSYM) {
			tok->datatype = sym->datatype->basicdt;
		} else if (typ->kind == BASICTYPE || typ->kind == POINTERSYM) {
			tok->datatype = typ->basicdt;
		}
	}

	return tok;
	
}
/* instconst installs a constant in the symbol table */
void  instconst(TOKEN idtok, TOKEN consttok) {
	SYMBOL sym, typesym;
	TOKEN temptok;
	
	if (consttok->tokentype == OPERATOR) {
		temptok = consttok->operands;
	} else {
		temptok = consttok;
	}
	sym = insertsym(idtok->stringval);
	if (temptok->tokentype == STRINGTOK) {
		typesym = searchst("char");
		strcpy(sym->constval.stringconst, temptok->stringval);
	} else if (temptok->tokentype == NUMBERTOK && temptok->datatype == REAL) {
		typesym = searchst("real");
		sym->constval.realnum = temptok->realval;
	} else if (temptok->tokentype == NUMBERTOK && temptok->datatype == INTEGER) {
		typesym = searchst("integer");
		sym->constval.intnum = temptok->intval;
	} else {
		yyerror("Invalid const");
		return;
	}	
	sym->kind = CONSTSYM;
	sym->datatype = typesym;
	sym->basicdt = typesym->basicdt;
}
/* makerepeat makes structures for a repeat statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr) {
	int cur_labelnumber = labelnumber;
	TOKEN tok1;
	TOKEN label_tok = makelabel();
	TOKEN goto_tok = makegoto(cur_labelnumber); 
	if (DEBUG & DB_REPEAT) {
		printf("initializing repeat\n");
		dbugprinttok(statements);
		dbugprinttok(expr);
	}
	makeprogn(tok, statements);
	tok1 = makeprogn(talloc(), 0);
	/* tokb has the if condition */
	makeif(tokb, expr, tok1, goto_tok);
	cons(tok, tokb);
	cons(label_tok, tok);
	return makeprogn(talloc(), label_tok);
}

/* makefloat forces the item tok to be floating, by floating a constant
   or by inserting a FLOATOP operator */
TOKEN makefloat(TOKEN tok) {
	TOKEN t1;
	if (tok->tokentype == NUMBERTOK && tok->datatype == INTEGER) {
		tok->datatype = REAL;
		tok->realval = tok->intval;
		t1 = tok;
	} else if ((tok->tokentype == IDENTIFIERTOK) && (tok->symentry->kind == VARSYM) && (tok->symentry->basicdt == INTEGER)) {
		t1 = makeop(FLOATOP);
		t1->operands = tok;
	} else if ((tok->tokentype == IDENTIFIERTOK) && (tok->symentry->kind == FUNCTIONSYM) && (tok->symentry->datatype != 0) &&
			(tok->symentry->basicdt == INTEGER)) {
		t1 = makeop(FLOATOP);
		t1->operands = tok;
	} else {
		t1 = makeop(FLOATOP);
		t1->operands = tok;
	}
	return t1;
}

/* makefix forces the item tok to be integer, by truncating a constant
   or by inserting a FIXOP operator */
TOKEN makefix(TOKEN tok) {
	TOKEN t1;
	if (tok->tokentype == NUMBERTOK && tok->datatype == REAL) {
		tok->datatype = INTEGER;
		tok->intval = tok->realval;
		t1 = tok;
	} else if ((tok->tokentype == IDENTIFIERTOK) && (tok->symentry->kind == VARSYM) && (tok->symentry->basicdt == REAL)) {
		t1 = makeop(FIXOP);
		t1->operands = tok;
	} else if ((tok->tokentype == IDENTIFIERTOK) && (tok->symentry->kind == FUNCTIONSYM) && (tok->symentry->datatype != 0) &&
			(tok->symentry->basicdt == REAL)) {
		t1 = makeop(FIXOP);
		t1->operands = tok;
	} else {
		t1 = makeop(FIXOP);
		t1->operands = tok;
	}
	return t1;
}


/* makewhile makes structures for a while statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) {
	int cur_labelnumber = labelnumber;
	TOKEN tok1;
	TOKEN label_tok = makelabel();		
	TOKEN goto_tok = makegoto(cur_labelnumber); 
	if (DEBUG & DB_WHILE) {
		printf("initializing while\n");			
		dbugprinttok(statement);
		dbugprinttok(expr);
	}
	makeprogn(tok, statement);
	/* tokb has the if condition */
	//tok1 = cons(tok, goto_tok);
	//if (DEBUG & DB_WHILE) {
		//printf("Trying to debug tok1\n");
		//dbugprinttok(tok1);
	//}
	tok->operands->link = goto_tok;
	makeif(tokb, expr, tok, 0);
	cons(label_tok, tokb);
	return makeprogn(talloc(), label_tok);
}

/* instlabel installs a user label into the label table */
void  instlabel (TOKEN num) {
	user_label[labelnumber++] = num->intval;
}

void inituserlabel() {
	int i;
	for (i = 0; i < MAX_USER_LABEL; i++) {
		user_label[i] = -1;
	}
}

/* 
 (progn (label 0)
       (:= (aref (^ fred)
            0)
         20))
 */
/* dolabel is the action for a label of the form   <number>: <statement>
   tok is a (now) unused token that is recycled. */
TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement) {
	int i;
	int found_label = 0;
	for (i = 0; (i < MAX_USER_LABEL) && (user_label[i] != -1); i++) {
		if (user_label[i] == labeltok->intval){
			found_label = 1;
			break;
		}
	}
	if (found_label == 0) {
		yyerror("undeclared label");
		return statement;
	} 
	TOKEN label = makeop(LABELOP);
	TOKEN labelnum = makeintc(i);
	unaryop(label, labelnum);
	tok = makeprogn(talloc(), label);
	tok->operands->link = statement;
	return tok;
}

/* dogoto is the action for a goto statement.
   tok is a (now) unused token that is recycled. */
TOKEN dogoto(TOKEN tok, TOKEN labeltok) {
	int i;
	int found_label = 0;
	for (i = 0; (i < MAX_USER_LABEL) && (user_label[i] != -1); i++) {
		if (user_label[i] == labeltok->intval){
			found_label = 1;
			break;
		}
	}
	if (found_label == 0) {
		yyerror("undeclared label");
		return tok;
	} 
	return makegoto(i);
}

/* instdotdot installs a .. subrange in the symbol table.
   dottok is a (now) unused token that is recycled. */
TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {
	return makesubrange(dottok, lowtok->intval, hightok->intval);
}

/* instarray installs an array declaration into the symbol table.
   bounds points to a SUBRANGE symbol table entry.
   The symbol table pointer is returned in token typetok. */
TOKEN instarray(TOKEN bounds, TOKEN typetok) {
	SYMBOL sym;
	SYMBOL sym1;
	TOKEN tok;
	TOKEN tok_type;
	sym = symalloc();
	if (bounds->link != 0) {
		tok_type = instarray(bounds->link, typetok);
	} else {
		tok_type = typetok;
	}
	if (bounds->symentry == 0) {
		findtype(bounds);
	}
	sym1 = bounds->symentry;
	sym->kind = ARRAYSYM;
	if (tok_type->symtype == 0) {
		findtype(tok_type);
	}
	sym->datatype = sym1;
	sym->size = (sym1->highbound - sym1->lowbound + 1) * tok_type->symtype->size;
	sym->highbound = sym1->highbound;
	sym->lowbound = sym1->lowbound;
    sym->datatype = tok_type->symtype;
	sym->basicdt = tok_type->symtype->basicdt;
	tok = copytok(tok_type);
	tok->symtype = sym;
	tok->symentry = sym;
	return tok;
}


/* makesubrange makes a SUBRANGE symbol table entry, puts the pointer to it
   into tok, and returns tok. */
TOKEN makesubrange(TOKEN tok, int low, int high) {
	SYMBOL sym;
	sym = symalloc();
	sym->lowbound = low;
	sym->highbound = high;
	sym->kind = SUBRANGE;
	sym->blocklevel = blocknumber;
	sym->size = 4;
	tok->symentry = sym;
	tok->symtype = sym;
	return tok;
}

/* instenum installs an enumerated subrange in the symbol table,
   e.g., type color = (red, white, blue)
   by calling makesubrange and returning the token it returns. */
TOKEN instenum(TOKEN idlist) {
	SYMBOL sym;
	SYMBOL typesym;
	int count = 0;
	TOKEN tok = idlist;
	typesym = searchst("integer");
	while (tok != 0) {
		sym = insertsym(tok->stringval);
		sym->kind = CONSTSYM;
		sym->datatype = typesym;
		sym->basicdt = typesym->basicdt;
		sym->blocklevel = blocknumber;
		
		sym->constval.intnum = count;
		tok = tok->link;
		count++;
	}
	return makesubrange(talloc(), 0, count-1);
}
 
/* insttype will install a type name in symbol table.
   typetok is a token containing symbol table pointers. */
void  insttype(TOKEN typename, TOKEN typetok){
	SYMBOL sym;
	TOKEN tok;
	TOKEN tok_type;
	sym = insertsym(typename->stringval);
	tok_type = typetok;
/*
	if (tok_type->symentry == 0) {
		findtype(tok_type);
	}
	*/
	sym->kind = TYPESYM;
	sym->datatype = tok_type->symtype;
	sym->size = tok_type->symtype->size;
	sym->basicdt = tok_type->symtype->basicdt;
	if (tok_type->symtype->kind == SUBRANGE) {
		sym->highbound = tok_type->symtype->highbound;
		sym->lowbound = tok_type->symtype->lowbound;
	} 
	typename->symtype = sym;
	typename->symentry = sym;	
	if (DEBUG & DB_TYPE) {
		printf("initializing type\n");			
		dbugprinttok(typename);
		dbugprinttok(typetok);
		printf("symbol type name is %s\n", sym->namestring);
	}
}

/* nconc concatenates two token lists, destructively, by making the last link
   of lista point to listb.
   (nconc '(a b) '(c d e))  =  (a b c d e)  */
/* nconc is useful for putting together two fieldlist groups to
   make them into a single list in a record declaration. */
TOKEN nconc(TOKEN lista, TOKEN listb) {
	TOKEN tok;
	tok = lista;
	while (tok->link != 0) {
		tok = tok->link;
	}
	tok->link = listb;
	return lista;
}

/* instrec will install a record definition.  Each token in the linked list
   argstok has a pointer its type.  rectok is just a trash token to be
   used to return the result in its symtype */
TOKEN instrec(TOKEN rectok, TOKEN argstok) {
	SYMBOL sym;
	int offset = 0;
	int size = 0;
	TOKEN tok = argstok;
	sym = symalloc();
	sym->kind = RECORDSYM;
	sym->blocklevel = blocknumber;
	while(tok != 0) {
		tok->symtype->offset = offset;
		size += tok->symtype->size;
		offset += tok->symtype->size;
		tok = tok->link;
	}
	sym->size = size;
	sym->datatype = argstok->symtype;
	rectok->symentry = sym;
	rectok->symtype = sym;
	return rectok;
}

/* instfields will install type in a list idlist of field name tokens:
   re, im: real    put the pointer to REAL in the RE, IM tokens.
   typetok is a token whose symtype is a symbol table pointer.
   Note that nconc() can be used to combine these lists after instrec() */
TOKEN instfields(TOKEN idlist, TOKEN typetok) {
	int symbol_size = 0;
	SYMBOL sym;
	SYMBOL sym_prev = 0;
	TOKEN tok = idlist;
	if (typetok->symtype == 0) {
		findtype(typetok); /* find type */
	}
	symbol_size = alignsize (typetok->symtype); /* find the size of type */
	while (tok != 0) {
		sym = symalloc();
		strcpy(sym->namestring, tok->stringval);
		/* Set up symbol as variable and initialize with block/symbol table info */	
		sym->kind = ARGSYM;
		sym->datatype = typetok->symtype;
		sym->size = typetok->symtype->size;
		sym->blocklevel = blocknumber;
	    sym->datatype = typetok->symtype;
		sym->basicdt = typetok->symtype->basicdt;
		tok->symentry = sym;
		tok->symtype = sym;
		tok = tok->link;
		
		if (sym_prev != 0) {
			sym_prev->link = sym;
		} 
		sym_prev = sym;
	}
	return idlist;
}


int wordaddress(int n, int wordsize)
  { return ((n + wordsize - 1) / wordsize) * wordsize; }
 
yyerror(s)
  char * s;
  { 
  fputs(s,stderr); putc('\n',stderr);
  }
main()
  { int res;
    initsyms();
    inituserlabel(); /* initializing user tabel */
    res = yyparse();
    printst();
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
  }