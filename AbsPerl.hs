

module AbsPerl where

-- Haskell module generated by the BNF converter
-- Adapted by I signori della droga

data Type 
    = T_Int
    | T_Float
    | T_Char
    | T_String
    | T_Void 
    | T_Bool
    | T_Error 
    | Pointer LExpr
    | ArrDef Type Integer
    deriving (Eq, Ord, Show)

newtype Ident = Ident String deriving (Eq, Ord, Show )
data Boolean = Boolean_True | Boolean_False
  deriving (Eq, Ord, Show)

data Program = Prog [Decl]
  deriving (Eq, Ord, Show )

data Decl
    = Dvar Type [VarDeclInit]
    | UndVar Type [UndVarDecl]
    | Dfun Type Ident [Parameter] [StmtDecl]
  deriving (Eq, Ord, Show )

data UndVarDecl = UndVarD UndArr | UndVarA UndVar
  deriving (Eq, Ord, Show )

data UndArr = UndA Ident
  deriving (Eq, Ord, Show )

data UndVar = UndV Ident
  deriving (Eq, Ord, Show )

data VarDeclInit
    = VarDeclInA VarDeclInitArray | VarDeclInV VarDeclInitVar
  deriving (Eq, Ord, Show )

data VarDeclInitArray = VarDeclInitAr Ident Array
  deriving (Eq, Ord, Show )

data VarDeclInitVar = VarDeclInitV Ident RExpr
  deriving (Eq, Ord, Show )

data Array = Arr [Array] | ArrE [RExpr]
  deriving (Eq, Ord, Show )

data Parameter = Param Modality Type Ident
  deriving (Eq, Ord, Show )

data Modality
    = M_Void
    | M_Val
    | M_Ref
    | M_Const
    | M_Res
    | M_Valres
    | M_Name
  deriving (Eq, Ord, Show)

data StmtDecl = Decls Decl | Stmts Stmt
  deriving (Eq, Ord, Show)

data Stmt
    = ProcCall FunCall
    | BlockDecl [StmtDecl]
    | Jmp JumpStmt
    | Iter IterStmt
    | Sel SelectionStmt
    | Assgn LExpr Assignment_op RExpr
    | LExprStmt LExpr
    | TryC TryCatch
  deriving (Eq, Ord, Show)

data Assignment_op
    = Assign
    | AssgnMul
    | AssgnAdd
    | AssgnDiv
    | AssgnSub
    | AssgnPow
    | AssgnAnd
    | AssgnOr
  deriving (Eq, Ord, Show )

data TryCatch = Try [StmtDecl] Type String [StmtDecl] -- typechecker verifica sia T_Err
  deriving (Eq, Ord, Show)

data JumpStmt = Break | Continue | RetExpVoid | RetExp RExpr
  deriving (Eq, Ord, Show )

data SelectionStmt
    = IfNoElse RExpr [StmtDecl]
    | ElseIf RExpr [StmtDecl] Elsif
  deriving (Eq, Ord, Show )

data Elsif 
    = IfElsIf RExpr [StmtDecl] Elsif 
    | EndElsIf [StmtDecl]
  deriving (Eq, Ord, Show )

data IterStmt
    = While RExpr [StmtDecl]
    | DoWhile [StmtDecl] RExpr
    | DoUntil [StmtDecl] RExpr
    | For ForStmtDecl RExpr ForStmt [StmtDecl]
    | ForEach ForStmt ForStmt [StmtDecl]
  deriving (Eq, Ord, Show )

data ForStmtDecl 
    = ForDeclInit Type Ident Assignment_op RExpr
    | Simple Ident Assignment_op RExpr 
  deriving (Eq, Ord, Show)

data ForStmt 
    = LexprForStmt LExpr
    | ForDecl Type Ident 
    | AssFor Ident Assignment_op RExpr
  deriving (Eq, Ord, Show)


data RExpr
    = InfixOp InfixOp RExpr RExpr
    | UnaryOp UnaryOp RExpr
    | Ref LExpr
    | FCall FunCall
    | Int Integer
    | Char Char
    | String String
    | Float Double
    | Bool Boolean
    | Lexpr LExpr
  deriving (Eq, Ord, Show)

data InfixOp = ArithOp ArithOp | RelOp RelOp | BoolOp BoolOp
  deriving (Eq,Ord,Show)

data ArithOp = Add | Sub | Mul | Div | Mod | Pow
  deriving (Eq,Ord,Show)

data BoolOp = And | Or | Xor 
  deriving (Eq,Ord,Show)

data RelOp = Eq | Neq | Lt | LtE | Gt | GtE
  deriving (Eq,Ord,Show)

data UnaryOp = Not | Neg
  deriving (Eq,Ord,Show)

data FunCall = Call Ident [RExpr]
  deriving (Eq, Ord, Show)

data LExpr
    = Deref LExpr
    | PrePostIncDecr PrePost IncDecr LExpr 
    | BasLExpr BLExpr
  deriving (Eq, Ord, Show)

data PrePost = Post | Pre
  deriving (Eq,Ord,Show)

data IncDecr = Inc | Decr
  deriving (Eq,Ord,Show)

data BLExpr = ArrayEl BLExpr RExpr | Id Ident
  deriving (Eq, Ord, Show )