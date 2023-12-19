%{
    open Ast
%}


%token Type             (** type - keyword *)
%token Of               (** of - keyword *)
%token Let              (** let - keyword *)
%token Rec              (** rec - keyword *)
%token In               (** in - keyword *)
%token If               (** if - keyword *)
%token Then             (** then - keyword *)
%token Else             (** else - keyword *)
%token Match            (** match - keyword *)
%token With             (** with - keyword *)
%token Fun              (** fun - keyword *)
%token Mod              (** mod - keyword *)


%token Eq               (** = - binary operator *)
%token Plus             (** + - binary operator *)
%token Minus            (** - - binary operator *)
%token Times            (** * - binary operator *)
%token Divide           (** / - binary operator *)
%token Lt               (** < - binary operator *)
%token Concat           (** ^ - binary operator *)
%token And              (** && - binary operator *)
%token Or               (** || - binary operator *)

%token Not              (** ! - unary operator *)
%token Negate           (** ~ - unary operator *)

%token DoubleSemicolon  (** ;; *)
%token Colon            (** : *)
%token Arrow            (** -> *)
%token DoubleArrow      (** => *)
%token LParen           (** ( *)
%token RParen           (** ) *)
%token Pipe             (** | *)
%token Comma            (** , *)

%token TInt             (** int - type name *)
%token TBool            (** bool - type name *)
%token TString          (** string - type name *)
%token TUnit            (** unit - type name *)

%token True             (** true - keyword *)
%token False            (** false - keyword *)
%token <string> Id     (** Identifier, like a variable or function name *)
%token <int> Int       (** Integer literal *)
%token <string> String (** String literal *)
%token EOF              (** End-of-file - you can ignore this *)

%start <ocaml_binding list> start

%type <ocaml_binding list> program
%type <ocaml_binding> binding
%type <param_type> type_branch
%type <param_type> param
%type <ocaml_expr> expr
%type <ocaml_expr> expr_app
%type <ocaml_expr> expr_base
%type <ocaml_match_branch> match_branch
%type <string list> match_vars
%type <ocaml_unop> unop
%type <ocaml_type_id> type_id
%type <ocaml_expr> unop_expr
%type <ocaml_expr> or_binop
%type <ocaml_expr> and_binop
%type <ocaml_expr> lteq_binop
%type <ocaml_expr> pmc_binop
%type <ocaml_expr> tdm_binop
%type <ocaml_type_id> base_type

%type <param_type list> list(param)
%type <string list> separated_nonempty_list(Comma,Id)
%type <ocaml_match_branch list> separated_nonempty_list(Pipe,match_branch)
%type <param_type list> separated_nonempty_list(Pipe,type_branch)
%type <ocaml_type_id list> separated_nonempty_list(Times,base_type)


%right Arrow
%right In


%%


start:
  | p = program; EOF; { p }

program:
  | b = binding; DoubleSemicolon; p = program; {b :: p}
  | b = binding; DoubleSemicolon; {[b]}

binding:
  | Let; var = Id; plist = list(param); Colon; ty = type_id; Eq; ex = expr; {OcamlLet (false, OVar (var), plist, Typeyes (ty), ex)}
  | Let; var = Id; plist = list(param);  Eq; ex = expr;                   {OcamlLet (false, OVar (var), plist, Typeno, ex)}
  | Let; Rec; var = Id; plist = list(param); Colon; ty = type_id; Eq; ex = expr;    {OcamlLet (true, OVar (var), plist, Typeyes (ty), ex)}
  | Let; Rec; var = Id; plist = list(param);  Eq; ex = expr;                       {OcamlLet (false, OVar (var), plist, Typeno, ex)}
  | Type; var = Id; Eq; Pipe; tbranch = separated_nonempty_list (Pipe, type_branch); {OcamlType (OVar (var), tbranch)}


type_branch:
 | var = Id; Of; typ = type_id; {PType (OVar (var), Typeyes (typ))}
 | var = Id;  {PType (OVar (var), Typeno)}

param:
| var = Id; {PType (OVar (var), Typeno)}
| LParen; var = Id; RParen; {PType (OVar (var), Typeno)}
| LParen; var = Id; Colon; ty = type_id; RParen; {PType (OVar (var), Typeyes (ty))}


expr:
  | Let; var = Id; plist = list(param); Colon; ty = type_id; Eq; ex1 = expr; In; ex2 = expr; {Letexpr (false, OVar (var), plist, Typeyes (ty), ex1, ex2)}
  | Let; var = Id; plist = list(param);  Eq; ex1 = expr; In; ex2 = expr;                   {Letexpr (false, OVar (var), plist, Typeno, ex1, ex2)}
  | Let; Rec; var = Id; plist = list(param); Colon; ty = type_id; Eq; ex1 = expr; In; ex2 = expr; {Letexpr (true, OVar (var), plist, Typeyes (ty), ex1, ex2)}
  | Let; Rec; var = Id; plist = list(param);  Eq; ex1 = expr; In; ex2 = expr;   {Letexpr (true, OVar (var), plist, Typeno, ex1, ex2)}
  | If; ex1 = expr; Then; ex2 = expr; Else; ex3 = expr; {Ifexpr (ex1, ex2, ex3)}
  | Fun; plist = nonempty_list (param); DoubleArrow; ex1 = expr;  {Funexpr (plist, Typeno, ex1)}
  | Fun; plist = nonempty_list (param); Colon; ty = type_id; DoubleArrow; ex1 = expr; {Funexpr (plist, Typeyes (ty), ex1)}
| Match; ex1 = expr; With; Pipe; mblist = separated_nonempty_list(Pipe, match_branch); {Matchexpr (ex1, mblist)}
| e1 = or_binop; {e1}


or_binop:
  | e1 = or_binop; Or; e2 = and_binop; {Binopexpr (e1, OrOp, e2)}
  | e1 = and_binop;   {e1}

and_binop:
  | e1 = and_binop; And; e2 = lteq_binop; {Binopexpr (e1, AndOp, e2)}
  | e1 = lteq_binop;  {e1}

lteq_binop:
  | e1 = lteq_binop; Lt; e2 = pmc_binop;  {Binopexpr (e1, Less, e2)}
  | e1 = lteq_binop; Eq; e2 = pmc_binop;  {Binopexpr (e1, Equal, e2)}
  | e1 = pmc_binop; {e1}

pmc_binop:
| e1 = pmc_binop; Plus; e2 = tdm_binop; {Binopexpr (e1, Add, e2)}
| e1 = pmc_binop; Minus; e2 = tdm_binop; {Binopexpr (e1, Sub, e2)}
| e1 = pmc_binop; Concat; e2 = tdm_binop; {Binopexpr (e1, Concatenate, e2)}
| e1 = tdm_binop; {e1}

tdm_binop:
| e1 = tdm_binop; Times; e2 = unop_expr;  {Binopexpr (e1, Mul, e2)}
| e1 = tdm_binop; Divide; e2 = unop_expr; {Binopexpr (e1, Div, e2)}
| e1 = tdm_binop; Mod; e2 = unop_expr; {Binopexpr (e1, Modulo, e2)}
| e1 = unop_expr; {e1}

unop_expr:
| n1 = unop; e1 = expr_app; {Unopexpr (n1, e1)}
| e1 = expr_app; {e1}

expr_app:
 | ex1 = expr_app; ex2 = expr_base; {FuncApp (ex1, ex2)}
 | ex1 = expr_base; {ex1}

expr_base:
| var = Int {Intliteral (var)}
| True; {Boolliteral (true)}
| False; {Boolliteral (false)}
| var = Id; {Idlit (OVar (var))}
| var = String; {Stringliteral (var)}
| LParen; e1=expr; Comma; e2 = separated_nonempty_list(Comma, expr); RParen; {Tupleliteral (e1 :: e2)}
| LParen; RParen; {EmptyExpr}
| LParen; ex = expr; RParen; {ex}


match_branch:
  | var = Id; vl = match_vars; DoubleArrow; ex1 = expr; {MBranch (OVar (var), vl, ex1)}
  | var = Id; DoubleArrow; ex1 = expr; {MBranch (OVar (var), [], ex1)}

match_vars:
  | LParen; vars = separated_nonempty_list(Comma, Id); RParen; {vars}
  | var = Id; {[var]}

unop:
| Not; {NotOp}
| Negate; {NegateOp}




type_id:
| t1 = base_type; Times; t2 = separated_nonempty_list (Times, base_type); {TupleTy (t1 :: t2)}
| t1 = base_type; {t1}

base_type:
| TInt; {IntTy}
| TBool; {BoolTy}
| TString;  {StringTy}
| TUnit;   {UnitTy}
| t1 = base_type; Arrow; t2 = base_type; {FunTy (t1, t2)}
| LParen; t1 = type_id; RParen; {t1}
| var = Id; {IdTy (var)}


