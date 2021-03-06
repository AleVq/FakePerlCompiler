-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParPerl where
import AbsPerl
import LexPerl
import ErrM

}

%name pProgram  Program
%name pStmt     Stmt
%name pRExpr    RExpr
%name pLExpr    LExpr
-- no lexer declaration
%monad          { Err } { thenM } { returnM }
%tokentype      {Token}
%token
  '!'           { PT _ (TS _ 1)  }
  '!='          { PT _ (TS _ 2)  }
  '$'           { PT _ (TS _ 3)  }
  '%'           { PT _ (TS _ 5)  }
  '&&'          { PT _ (TS _ 6)  }
  '&='          { PT _ (TS _ 7)  }
  '('           { PT _ (TS _ 8)  }
  ')'           { PT _ (TS _ 9)  }
  '*'           { PT _ (TS _ 10) }
  '**'          { PT _ (TS _ 11) }
  '**='         { PT _ (TS _ 12) }
  '*='          { PT _ (TS _ 13) }
  '+'           { PT _ (TS _ 14) }
  '++'          { PT _ (TS _ 15) }
  '+='          { PT _ (TS _ 16) }
  ','           { PT _ (TS _ 17) }
  '-'           { PT _ (TS _ 18) }
  '--'          { PT _ (TS _ 19) }
  '-='          { PT _ (TS _ 20) }
  '/'           { PT _ (TS _ 21) }
  '/='          { PT _ (TS _ 22) }
  ';'           { PT _ (TS _ 23) }
  '<'           { PT _ (TS _ 24) }
  '<='          { PT _ (TS _ 25) }
  '='           { PT _ (TS _ 26) }
  '=='          { PT _ (TS _ 27) }
  '>'           { PT _ (TS _ 28) }
  '>='          { PT _ (TS _ 29) }
  '@'           { PT _ (TS _ 30) }
  'Exception'   { PT _ (TS _ 31) }
  'False'       { PT _ (TS _ 32) }
  'True'        { PT _ (TS _ 33) }
  '['           { PT _ (TS _ 34) }
  '\\'          { PT _ (TS _ 35) }
  ']'           { PT _ (TS _ 36) }
  'bool'        { PT _ (TS _ 37) }
  'break'       { PT _ (TS _ 38) }
  'catch'       { PT _ (TS _ 39) }
  'char'        { PT _ (TS _ 40) }
  'const'       { PT _ (TS _ 41) }
  'continue'    { PT _ (TS _ 42) }
  'do'          { PT _ (TS _ 43) }
  'else'        { PT _ (TS _ 44) }
  'elsif'       { PT _ (TS _ 45) }
  'float'       { PT _ (TS _ 46) }
  'for'         { PT _ (TS _ 47) }
  'foreach'     { PT _ (TS _ 48) }
  'if'          { PT _ (TS _ 49) }
  'int'         { PT _ (TS _ 50) }
  'my'          { PT _ (TS _ 51) }
  'name'        { PT _ (TS _ 52) }
  'ref'         { PT _ (TS _ 53) }
  'res'         { PT _ (TS _ 54) }
  'return'      { PT _ (TS _ 55) }
  'string'      { PT _ (TS _ 56) }
  'sub'         { PT _ (TS _ 57) }
  'try'         { PT _ (TS _ 58) }
  'until'       { PT _ (TS _ 59) }
  'val'         { PT _ (TS _ 60) }
  'valres'      { PT _ (TS _ 61) }
  'void'        { PT _ (TS _ 62) }
  'while'       { PT _ (TS _ 63) }
  '{'           { PT _ (TS _ 64) }
  '|='          { PT _ (TS _ 65) }
  '||'          { PT _ (TS _ 66) }
  '}'           { PT _ (TS _ 67) }

L_integ         { PT _ (TI $$)   }
L_charac        { PT _ (TC $$)   }
L_quoted        { PT _ (TL $$)   }
L_doubl         { PT _ (TD $$)   }
L_ident         { PT _ (TV $$)   }

%left           '||'
%left           '&&'
%left           '!'
%nonassoc       '==' '!=' '<' '<=' '>' '>='
%left           '+' '-'
%left           '*' '/' '%'
%right          '**'
%left           NEG
%right          '$'

%%

Integer :: { Integer } : L_integ                    { (read ($1)) :: Integer }
Char    :: { Char }    : L_charac                   { (read ($1)) :: Char    }
String  :: { String }  : L_quoted                   { $1                     }
Double  :: { Double }  : L_doubl                    { (read ($1)) :: Double  }
Ident   :: { Ident }   : L_ident                    { Ident $1               }

Boolean :: { Boolean }
Boolean : 'True'                                    { AbsPerl.Boolean_True                (posLine $1) }
        | 'False'                                   { AbsPerl.Boolean_False               (posLine $1) }

Type :: { Type }
Type : Type '[' Integer ']'                         { AbsPerl.ArrDef           $1 $3 }
      | '\\' Type                                   { AbsPerl.Pointer          $2    }
      | 'bool'                                      { T_Bool   }
      | 'char'                                      { T_Char   }
      | 'float'                                     { T_Float  }
      | 'int'                                       { T_Int    }
      | 'void'                                      { T_Void   }
      | 'string'                                    { T_String }
      | 'Exception'                                 { T_Error  }

RExpr :: { RExpr }
RExpr : '(' RExpr ')'                               { Rexpr                    $2         (posLine $3) }
      | RExpr '||' RExpr                            { InfixOp (BoolOp Or)      $1  $3     (posLine $2) }
      | RExpr '&&' RExpr                            { InfixOp (BoolOp And)     $1  $3     (posLine $2) }
      | RExpr '==' RExpr                            { InfixOp (RelOp Eq)       $1  $3     (posLine $2) }
      | RExpr '!=' RExpr                            { InfixOp (RelOp Neq)      $1  $3     (posLine $2) }
      | RExpr '<'  RExpr                            { InfixOp (RelOp Lt)       $1  $3     (posLine $2) }
      | RExpr '<=' RExpr                            { InfixOp (RelOp LtE)      $1  $3     (posLine $2) }
      | RExpr '>'  RExpr                            { InfixOp (RelOp Gt)       $1  $3     (posLine $2) }
      | RExpr '>=' RExpr                            { InfixOp (RelOp GtE)      $1  $3     (posLine $2) }
      | RExpr '+'  RExpr                            { InfixOp (ArithOp Add)    $1  $3     (posLine $2) }
      | RExpr '-'  RExpr                            { InfixOp (ArithOp Sub)    $1  $3     (posLine $2) }
      | RExpr '*'  RExpr                            { InfixOp (ArithOp Mul)    $1  $3     (posLine $2) }
      | RExpr '/'  RExpr                            { InfixOp (ArithOp Div)    $1  $3     (posLine $2) }
      | RExpr '%'  RExpr                            { InfixOp (ArithOp Mod)    $1  $3     (posLine $2) }
      | RExpr '**' RExpr                            { InfixOp (ArithOp Pow)    $1  $3     (posLine $2) }
      | '!' RExpr                                   { UnaryOp Not              $2         (posLine $1) }
      | '-' RExpr %prec NEG                         { UnaryOp Neg              $2         (posLine $1) }
      | '\\' LExpr                                  { Ref                      $2         (posLine $1) }
      | LExpr                                       { Lexpr                    $1                      }
      | FunCall                                     { FCall                    $1                      }
      | Const                                       { Const                    $1                      }

Const :: { Const }
Const : Integer                                     { AbsPerl.Int              $1                      }
      | Char                                        { AbsPerl.Char             $1                      }
      | String                                      { AbsPerl.String           $1                      }
      | Double                                      { AbsPerl.Float            $1                      }
      | Boolean                                     { AbsPerl.Bool             $1                      }

FunCall :: { FunCall }
FunCall : Ident '(' ListRExpr ')'                   { AbsPerl.Call             $1 $3      (posLine $4) }

ListRExpr :: { [RExpr] }
ListRExpr : {- empty -}                             { [] }
          | RExpr                                   { (:[])                    $1    }
          | RExpr ',' ListRExpr                     { (:)                      $1 $3 }

LExpr :: { LExpr }
LExpr : LExpr1                                      { $1 }
      | '$' LExpr                                   { AbsPerl.Deref            $2         (posLine $1) }
      | '++' LExpr1                                 { PrePostIncDecr Pre Inc   $2         (posLine $1) }
      | '--' LExpr1                                 { PrePostIncDecr Pre Decr  $2         (posLine $1) }

LExpr1 :: { LExpr }
LExpr1 : LExpr2                                     { $1 }
       | LExpr2 '++'                                { PrePostIncDecr Post Inc  $1         (posLine $2) }
       | LExpr2 '--'                                { PrePostIncDecr Post Decr $1         (posLine $2) }

LExpr2 :: { LExpr }
LExpr2 : '(' LExpr ')'                              { Lex                      $2         (posLine $3) }
       | BLExpr                                     { AbsPerl.BasLExpr         $1                      }

BLExpr :: { BLExpr }
BLExpr : BLExpr '[' RExpr ']'                       { AbsPerl.ArrayEl          $1 $3      (posLine $4) }
       | DolOrAt  Ident                                { AbsPerl.Id               $1 $2                }

DolOrAt :: { DolOrAt }
DolOrAt : '$'                                 { AbsPerl.Dollar                                }
        | '@'                                 { AbsPerl.At                                    }

Program :: { Program }
Program : ListDecl                                  { AbsPerl.Prog             (reverse $1)             }

ListDecl :: { [Decl] }
ListDecl : {- empty -}                              { [] } 
         | ListDecl Decl                            { flip (:)                 $1 $2 }

Decl :: { Decl }
Decl : 'sub' Type Ident '(' ListParameter ')' '{' ListStmtDecl '}'
                                                    { AbsPerl.Dfun             $2 $3      (posLine $1) $5 (reverse $8) }
     | 'my' Type ListVarDeclInit ';'                { AbsPerl.Dvar             $2         (posLine $1) $3              }
     | 'my' Type ListUndVarDecl  ';'                { AbsPerl.UndVar           $2         (posLine $1) $3              }

ListVarDeclInit :: { [VarDeclInit] }
ListVarDeclInit : VarDeclInit                       { (:[])                    $1    }
                | VarDeclInit ',' ListVarDeclInit   { (:)                      $1 $3 }

ListUndVarDecl :: { [UndVarDecl] }
ListUndVarDecl : UndVarDecl                         { (:[])                    $1    }
               | UndVarDecl ',' ListUndVarDecl      { (:)                      $1 $3 }

UndVarDecl :: { UndVarDecl }
UndVarDecl : UndArr                                 { AbsPerl.UndVarD          $1    }
           | UndVar                                 { AbsPerl.UndVarA          $1    }

VarDeclInit :: { VarDeclInit }
VarDeclInit : VarDeclInitArray                      { AbsPerl.VarDeclInA       $1    }
            | VarDeclInitVar                        { AbsPerl.VarDeclInV       $1    }

UndArr :: { UndArr }
UndArr : '@' Ident                                  { AbsPerl.UndA             $2         (posLine $1) }

UndVar :: { UndVar }
UndVar : '$' Ident                                  { AbsPerl.UndV             $2         (posLine $1) }

VarDeclInitArray :: { VarDeclInitArray }
VarDeclInitArray : '@' Ident '=' '(' Array ')'      { AbsPerl.VarDeclInitAr    $2 $5      (posLine $1) }

VarDeclInitVar :: { VarDeclInitVar }
VarDeclInitVar : '$' Ident '=' RExpr                { AbsPerl.VarDeclInitV     $2 $4      (posLine $1) }

ListArray :: { [Array] }
ListArray : Array                                   { (:[])                    $1    }
          | Array ',' ListArray                     { (:)                      $1 $3 }

Array :: { Array }
Array : '(' ListArray ')'                           { AbsPerl.Arr              $2         (posLine $3) }
      | ListRExpr                                   { AbsPerl.ArrE             $1                      }

ListParameter :: { [Parameter] }
ListParameter : {- empty -}                         { [] }
              | Parameter                           { (:[])                    $1    }
              | Parameter ',' ListParameter         { (:)                      $1 $3 }

Parameter :: { Parameter }
Parameter : Modality Type DolOrAt Ident                      { AbsPerl.Param            $1 $2 $3 $4           }

Modality :: { Modality }
Modality : {- empty -}                              { M_Void }
         | 'val'                                    { M_Val                               (posLine $1) }
         | 'ref'                                    { M_Ref                               (posLine $1) }
         | 'const'                                  { M_Const                             (posLine $1) }
         | 'res'                                    { M_Res                               (posLine $1) }
         | 'valres'                                 { M_Valres                            (posLine $1) }
         | 'name'                                   { M_Name                              (posLine $1) }

ListStmtDecl :: { [StmtDecl] }
ListStmtDecl : {- empty -}                          { [] }
             | ListStmtDecl StmtDecl                { flip (:)                 $1 $2 }

StmtDecl :: { StmtDecl }
StmtDecl : Decl                                     { AbsPerl.Decls            $1    }
         | Stmt                                     { AbsPerl.Stmts            $1    }

Stmt :: { Stmt }
Stmt : FunCall ';'                                  { AbsPerl.ProcCall         $1         (posLine $2)              }
     | '{' ListStmtDecl '}'                         { AbsPerl.BlockDecl                   (posLine $1) (reverse $2) }
     | JumpStmt ';'                                 { AbsPerl.Jmp              $1                                   }
     | IterStmt                                     { AbsPerl.Iter             $1                                   }
     | SelectionStmt                                { AbsPerl.Sel              $1                                   }
     | TryCatch                                     { AbsPerl.TryC             $1                                   }
     | LExpr Assignment_op RExpr ';'                { AbsPerl.Assgn            $1 $2 $3   (posLine $4)              }
     | LExpr ';'                                    { AbsPerl.LExprStmt        $1         (posLine $2)              }

Assignment_op :: { Assignment_op }
Assignment_op : '='                                 { AbsPerl.Assign                      (posLine $1) }
              | '*='                                { AbsPerl.AssgnMul                    (posLine $1) }
              | '+='                                { AbsPerl.AssgnAdd                    (posLine $1) }
              | '/='                                { AbsPerl.AssgnDiv                    (posLine $1) }
              | '-='                                { AbsPerl.AssgnSub                    (posLine $1) }
              | '**='                               { AbsPerl.AssgnPow                    (posLine $1) }
              | '&='                                { AbsPerl.AssgnAnd                    (posLine $1) }
              | '|='                                { AbsPerl.AssgnOr                     (posLine $1) }

TryCatch :: { TryCatch }
TryCatch : 'try' '{' ListStmtDecl '}' 'catch' '(' Type String ')' '{' ListStmtDecl '}'
                                                                        { AbsPerl.Try                       (posLine $1) (reverse $3) $7 $8 (posLine $5) (reverse $11) }

SelectionStmt :: { SelectionStmt }
SelectionStmt : 'if' '(' RExpr ')' '{' ListStmtDecl '}'                 { AbsPerl.IfNoElse $3               (posLine $1) (reverse $6)    }
              | 'if' '(' RExpr ')' '{' ListStmtDecl '}' Elsif           { AbsPerl.IfElsIf $3                (posLine $1) (reverse $6) $8 }

Elsif :: { Elsif }
Elsif : 'elsif' '(' RExpr ')' '{' ListStmtDecl '}' Elsif                { AbsPerl.ElsIf $3                  (posLine $1) (reverse $6) $8 }
      | 'else' '{' ListStmtDecl '}'                                     { AbsPerl.EndElsIf                  (posLine $1) (reverse $3)    }

IterStmt :: { IterStmt }
IterStmt : 'for' '(' ForStmtDecl ';' RExpr ';' ForStmt ')' '{' ListIterStmtDecl '}'
                                                                        { AbsPerl.For $3 $5 $7              (posLine $1) (reverse $10)   }
         | 'foreach' ForStmt '(' ForStmt ')' '{' ListIterStmtDecl '}'   { AbsPerl.ForEach $2 $4             (posLine $1) (reverse $7)    }
         | 'while' '(' RExpr ')' '{' ListIterStmtDecl '}'               { AbsPerl.While $3                  (posLine $1) (reverse $6)    }
         | 'do' '{' ListIterStmtDecl '}' 'while' '(' RExpr ')' ';'      { AbsPerl.DoWhile (reverse $3) $7   (posLine $1)                 }
         | 'do' '{' ListIterStmtDecl '}' 'until' '(' RExpr ')' ';'      { AbsPerl.DoUntil (reverse $3) $7   (posLine $1)                 }

IterStmtDecl :: {IterStmtDecl}
IterStmtDecl : 'break'                                                  { AbsPerl.Break                     (posLine $1) }
             | 'continue'                                               { AbsPerl.Continue                  (posLine $1) }
             | StmtDecl                                                 { AbsPerl.ItStDe $1}

ListIterStmtDecl :: { [IterStmtDecl] }
ListIterStmtDecl : {- empty -} { [] }
                 | ListIterStmtDecl IterStmtDecl { flip (:) $1 $2 }

ForStmtDecl :: {ForStmtDecl}
ForStmtDecl : 'my' Type '$' Ident Assignment_op RExpr                   { AbsPerl.ForDeclInit $2 $4 $5 $6   (posLine $1) }
            | '$' Ident Assignment_op RExpr                             { AbsPerl.Simple $2 $3 $4           (posLine $1) }

ForStmt :: {ForStmt}
ForStmt : LExpr                                                         { AbsPerl.LexprForStmt $1 }
        | 'my' Type '$' Ident                                           { AbsPerl.ForDecl $2 $4             (posLine $1) }
        | Ident Assignment_op RExpr                                     { AbsPerl.AssFor $1 $2 $3 }

JumpStmt :: { JumpStmt }
JumpStmt : 'return'                                                     { AbsPerl.RetExpVoid                (posLine $1) }
         | 'return' RExpr                                               { AbsPerl.RetExp $2                 (posLine $1) }

{
returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    t:_ -> " before `" ++ id(prToken t) ++ "'"

myLexer = tokens
}
