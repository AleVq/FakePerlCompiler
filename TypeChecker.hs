module TypeChecker where

import AbsPerl 
import PrintPerl
import ErrM
import Control.Monad

type Fun = (Ident, (Type, [(Type, Modality)]))
{- se una variabile è indefinita Def = False, quindi non può essere assegnata da un'altra
variabile -}
type Var = (Ident, (Type, Def))
type Def = Bool

type Env = [ ([Fun],[Var]) ]

{- enviroment iniziale con funzioni di default -}
emptyEnv = [ ([],[]) ]

typechecker :: Program -> Err Env
typechecker (Prog []) = Ok emptyEnv
typechecker (Prog decls) =
    do
        {- aggiungiamo prima le signature delle funzioni in modo da garantire mutua ricorsione -}
        env1 <- addFun emptyEnv (Ident "writeInt") T_Void [Param (M_Val 0) T_Int (Ident "x")] 0
        env2 <- addFun emptyEnv (Ident "writeFloat") T_Void [Param (M_Val 0) T_Float (Ident "x")] 0
        env3 <- addFun emptyEnv (Ident "writeChar") T_Void [Param (M_Val 0) T_Char (Ident "x")] 0
        env4 <- addFun emptyEnv (Ident "writeString") T_Void [Param (M_Val 0) T_String (Ident "x")] 0
        env5 <- addFun emptyEnv (Ident "readInt") T_Int [] 0
        env6 <- addFun emptyEnv (Ident "readFloat") T_Float [] 0
        env7 <- addFun emptyEnv (Ident "readChar") T_Char [] 0
        env8 <- addFun emptyEnv (Ident "readString") T_String [] 0
        env <- checkFunDefs env8 decls
        checkDecls env decls

addScope :: Env -> Err Env 
addScope env = Ok ( ([],[]) : env )

remScope :: Env -> Err Env
remScope [] = Bad ("erroe\n")
remScope (scope:scopes) = Ok scopes



addVar :: Env -> Ident -> Type -> Def -> Int -> Err Env
addVar (scope:scopes) id typ def pos = 
    case lookup id (snd scope) of
        Nothing -> Ok ((fst scope, (id, (typ, def)) : (snd scope)) : scopes)
        Just _ -> Bad ("Error : variable " ++  printTree id ++ " at line " ++ show pos ++ "already declared\n")

addVars :: Env -> [Ident] -> Type -> Def -> [Int] -> Err Env
addVars env [] _ _ _ = Ok env
addVars env (id:ids) typ def (pos:poss) =
    do
        env_ <- addVar env id typ def pos
        addVars env_ ids typ def poss

addFun :: Env -> Ident -> Type -> [Parameter] -> Int -> Err Env
addFun env@(scope:scopes) id typ param pos = 
    case lookup id (fst scope) of
        Nothing ->
            do 
                let sig = (typ, map (\(Param mod typ id) -> (typ, mod)) param)
                Ok ((\(scope:scopes) -> ((id, sig):fst scope, snd scope):scopes) env)

        Just _ -> Bad("Error : function " ++ printTree id ++ " at line " ++ show pos ++ "already declared\n")

checkFunDefs :: Env -> [Decl] -> Err Env 
checkFunDefs env [] = Ok env
checkFunDefs env (decl:decls) =
    do 
        env_ <- checkFunDef env decl
        checkFunDefs env decls

checkFunDef :: Env -> Decl -> Err Env 
checkFunDef env decl =
    case decl of
        Dfun typ id pos param _ -> addFun env id typ param pos
        _ -> Ok env 

checkFunStmts :: Env -> [StmtDecl] -> Err Env 
checkFunStmts env [] = Ok env
checkFunStmts env (stmt_decl:stmts_decls) =
    do 
        env_ <- checkFunStmt env stmt_decl
        checkFunStmts env stmts_decls

checkFunStmt :: Env -> StmtDecl -> Err Env 
checkFunStmt env stmt_decl =
    case stmt_decl of
        Decls (Dfun typ id pos param _) -> addFun env id typ param pos
        _ -> Ok env 

checkDecls :: Env -> [Decl] -> Err Env
checkDecls env [] = Ok env
checkDecls env (decl:decls) =
    case decl of
        Dvar typ _ vardecl -> 
            do 
                env_ <- checkVarInit env vardecl typ
                checkDecls env decls
        UndVar typ _ undvardecl ->
            do 
                env_ <- addVars env (map getIdUndVar undvardecl) typ False (map getLineUndVar undvardecl)
                checkDecls env decls
        Dfun typ id pos param stmts_decls ->
            do 
                env2 <- addScope env 
                env3 <- foldM (\env (Param mod typ id) -> addVar env id typ True pos) env2 param
                env4 <- checkFunStmts env3 stmts_decls
                checkStmtsDecls env4 stmts_decls typ pos
                env5 <- remScope env4
                checkDecls env5 decls
    where 
        getIdUndVar :: UndVarDecl -> Ident 
        getIdUndVar undvard =
            case undvard of 
                UndVarD (UndA id _) -> id 
                UndVarA (UndV id _) -> id 
        getLineUndVar :: UndVarDecl -> Int
        getLineUndVar undvard =
            case undvard of 
                UndVarD (UndA _ l) -> l
                UndVarA (UndV _ l) -> l 

checkVarInit :: Env -> [VarDeclInit] -> Type -> Err Env 
checkVarInit env [] _ = Ok env
checkVarInit env (vardin:varsdin) typ = 
    case vardin of
        VarDeclInA (VarDeclInitAr id array pos) -> checkArray env id typ pos array 
        VarDeclInV (VarDeclInitV id rexpr pos) -> 
            do 
                let typ_ = checkRExpr env rexpr
                case checkType typ_ (Ok typ) of
                    Just t -> Ok env
                    Nothing -> Bad ("Error : value assigned to variable " ++ printTree id ++ "declared at line " ++ show pos ++ "should have type" ++ printTree typ
                               ++ " but has type " ++ printTree ( (\(Ok typ) -> typ) typ_ ) ++ "\n")
        
checkArray :: Env -> Ident  -> Type -> Int -> Array -> Err Env 
checkArray env id typ pos array= 
    case array of 
        ArrE rexprs -> 
            do
                let typ_ = checkRExprs env rexprs
                case checkType typ_ (Ok typ) of
                    Just t -> Ok env 
                    Nothing -> Bad ("Error : while initializing array " ++ printTree id ++ " declared at line " ++ show pos ++ " element's type should be" ++ printTree typ
                               ++ " but found " ++ printTree ( (\(Ok typ) -> typ) typ_ ) )
        Arr array _ ->  ((\([Ok env_]) -> Ok env)( map (checkArray env id typ pos) array ))

checkStmtsDecls :: Env -> [StmtDecl] -> Type -> Int -> Err Env 
checkStmtsDecls env [] typ _ = Ok env
checkStmtsDecls env (stmt_decl:stmts_decls) typ pos = 
    case stmt_decl of
        Decls decl ->
            do 
                env_ <- checkDecls env (decl :[])
                checkStmtsDecls env_ stmts_decls typ pos 
        Stmts stmt -> 
            do
                env_ <- checkStmt env stmt typ pos 
                checkStmtsDecls env_ stmts_decls typ pos

checkStmt :: Env -> Stmt -> Type -> Int -> Err Env
checkStmt env stmt typ pos =
    case stmt of
        ProcCall (Call id rexprs pos) _ -> 
            case lookupFun env id rexprs of
                Just typ -> Ok env 
                Nothing -> Bad ("Error : function used at line " ++ show pos ++ " is not declared\n") 
        BlockDecl p stmts_decls -> checkStmtsDecls env stmts_decls typ pos
        Jmp jmpstmt ->
            case jmpstmt of
                RetExpVoid p ->
                    case typ of
                        T_Void  -> Ok env
                        _ -> Bad ("Error : function declared at line " ++ show pos ++ " is not of type void as suggeste ad line " ++ show p ++ 
                                  " by the return statement\n")
                RetExp rexpr p -> 
                    do 
                        let typ_ = checkRExpr env rexpr 
                        case checkType typ_ (Ok typ) of 
                            Just _ -> Ok env
                            Nothing -> Bad ("Error : function declared at line " ++ show pos ++ " is not of type " ++ printTree typ ++ " as suggeste ad line " 
                                       ++ show p ++ " by the return statement\n")
        Iter iterstmt -> 
            case iterstmt of
                While rexpr p stmts_decls -> 
                    case checkRExpr env rexpr of 
                        Ok T_Bool -> checkIterStmtsDecls env stmts_decls typ pos 
                        _ -> Bad ("Error : invalid guard of while statement at line " ++ show p)
                DoWhile stmts_decls rexpr p -> 
                    case checkRExpr env rexpr of 
                        Ok T_Bool -> checkIterStmtsDecls env stmts_decls typ pos 
                        _ -> Bad ("Error : invalid guard of do-while statement at line " ++ show p)
                DoUntil stmts_decls rexpr p -> 
                    case checkRExpr env rexpr of 
                        Ok T_Bool -> checkIterStmtsDecls env stmts_decls typ pos 
                        _ -> Bad ("Error : invalid guard of do-until statement at line " ++ show p)
                ForEach forstmt forstmt_ p stmts_decls ->
                    case forstmt of 
                        ForDecl typ_ id p_ ->
                            case forstmt_ of 
                                LexprForStmt lexpr ->
                                    case checkLExpr env lexpr of 
                                        Ok (ArrDef typ__ _) ->
                                            case checkType (Ok typ_) (Ok typ__) of 
                                                Just _ -> checkIterStmtsDecls env stmts_decls typ pos
                                                Nothing -> Bad ("Error : in for each statement at line " ++ show p_ ++ " variable " ++ printTree id ++ "(" ++ printTree typ_ ++ ")" 
                                                            ++ " is not of the same type of var " ++ printTree id ++ "(" ++ printTree typ__ ++ ")\n" ) 
                                        Ok _ -> Bad("Error : in for each statement at line " ++ show p_ ++ " iterable shold be and array\n")
                                        _ -> Bad("Error : in for statement at line " ++ show p_ ++ " iterable not correctly defined\n")
                                _ -> Bad("Error : in for statement at line " ++ show p_ ++ " iterable not correctly defined\n")
                        _ -> Bad ("Error : invalid guard in for each statement at line " ++ show p ++ "\n")
                For  forstmtdecl rexpr forstmt p stmts_decls -> 
                    case checkRExpr env rexpr of
                        Ok T_Bool ->
                            case forstmtdecl of 
                                ForDeclInit typ id ass rexpr _ -> 
                                    case ass of 
                                        Assign _ ->                                                                
                                             case checkRExpr env rexpr of
                                                Ok typ_ -> 
                                                    case (checkType (Ok typ_ ) (Ok typ) )of 
                                                        Just _ -> 
                                                            case forstmt of 
                                                                AssFor id_ _ rexpr ->
                                                                 if (id == id_) then
                                                                    do
                                                                        let typ_ = checkRExpr env rexpr
                                                                        case checkType typ_ (Ok typ) of 
                                                                            Just _ -> checkIterStmtsDecls env stmts_decls typ pos
                                                                            Nothing -> Bad ("Errore\n")
                                                                  else 
                                                                        Bad ("Errore\n")
                                                                LexprForStmt lexpr -> 
                                                                    case lexpr of
                                                                        PrePostIncDecr _ _ lexpr _ ->
                                                                            do 
                                                                                let typ_ = checkLExpr env lexpr
                                                                                case checkType typ_ (Ok typ) of
                                                                                    Just _ -> checkIterStmtsDecls env stmts_decls typ pos
                                                                                    Nothing ->  Bad ("Errore\n")
                                                                        _ ->  Bad ("Errore\n")
                                                                _ ->  Bad ("Errore\n")
                                                        Nothing ->  Bad ("Errore\n")
                                        _ ->  Bad ("Errore\n")
                                Simple id _ rexpr p ->
                                    do
                                        env_ <- signAsDef env id 
                                        case lookupVar env_ id of 
                                            Just typ  -> 
                                                do 
                                                    let typ_ = checkRExpr env rexpr 
                                                    case checkType typ_ (Ok typ) of 
                                                        Just _ ->  
                                                            case forstmt of 
                                                                AssFor id_ _ rexpr ->
                                                                 if (id == id_) then
                                                                    do
                                                                        let typ_ = checkRExpr env rexpr
                                                                        case checkType typ_ (Ok typ) of 
                                                                            Just _ -> checkIterStmtsDecls env stmts_decls typ pos
                                                                            Nothing -> Bad ("Errore\n")
                                                                  else 
                                                                        Bad ("Errore\n")
                                                                LexprForStmt lexpr -> 
                                                                    case lexpr of
                                                                        PrePostIncDecr _ _ lexpr _ ->
                                                                            do 
                                                                                let typ_ = checkLExpr env lexpr
                                                                                case checkType typ_ (Ok typ) of
                                                                                    Just _ -> checkIterStmtsDecls env stmts_decls typ pos
                                                                                    Nothing ->  Bad ("Errore\n")
                                                                        _ ->  Bad ("Errore\n")
                                                                _ ->  Bad ("Errore\n")
                                                        Nothing -> Bad ("Errore\n")
                                            Nothing -> Bad ("Errore\n")
                        _ -> Bad ("Error : invalid declaration of guard for loop statement at line" ++ show p ++ "\n")
        Sel selectionstmt ->
            case selectionstmt of
                IfNoElse rexpr p stmts_decls ->
                    case checkRExpr env rexpr of
                        Ok T_Bool -> checkStmtsDecls env stmts_decls typ pos
                        _ -> Bad("Error : invalid declaration of if condition at line " ++ show p ++ "\n" )
                IfElsIf rexpr p stmts_decls elsif ->
                    case checkRExpr env rexpr of 
                        Ok T_Bool -> 
                            do 
                                env_ <- checkStmtsDecls env stmts_decls typ pos
                                checkElsif env_ elsif typ pos 
                        _ -> Bad("Error : invalid declaration of if condition at line " ++ show p ++ "\n" )
        Assgn lexpr ass rexpr p -> 
            case checkLExpr env lexpr of 
                Ok T_Error  -> 
                    case ass of 
                        Assign _ -> 
                            do
                                {-env_ <- signAsDef env (getIdLexpr lexpr)-}
                                checkStmt env stmt typ pos
                Ok typ_  ->     
                    do
                        let typ__ = checkRExpr env rexpr 
                        case checkType (Ok typ_) typ__ of 
                            Just _ -> Ok env 
                            Nothing -> Bad ("Error : bad typing at line " ++ show p ++ " in assignement of var " ++ printTree  (getIdLexpr lexpr)
                                      ++ " of typ " ++ printTree typ_ ++ "\n")
        TryC (Try _ stmts_decls typ _ p stmts_decls_) ->
            do 
                env_ <- checkStmtsDecls env stmts_decls typ pos 
                case typ of
                    T_Error -> checkStmtsDecls env_ stmts_decls_ typ pos
                    _ -> Bad ("Error : incorrect declaration of catch exception at line " ++ show p ++ "\n")
        LExprStmt lexpr p -> if (checkLExpr env lexpr == Ok typ) then 
                                Ok env
                             else 
                                Bad ("Error at line ...")
    where 
        checkElsif :: Env -> Elsif -> Type -> Int -> Err Env 
        checkElsif env elsif typ pos = 
            case elsif of 
                ElsIf rexpr p stmts_decls elsif ->
                    case checkRExpr env rexpr of 
                        Ok T_Bool -> 
                            do 
                                env_ <- checkStmtsDecls env stmts_decls typ pos
                                checkElsif env_ elsif typ pos
                        _ -> Bad("Error : invalid declaration of else-if condition at line " ++ show p ++ "\n" )  
                EndElsIf p stmts_decls -> checkStmtsDecls env stmts_decls typ pos

signAsDef :: Env -> Ident -> Err Env 
signAsDef [] _ = Bad ("Error in code\n")
signAsDef env id = Ok (map (mylookup id) env)
    where 
        mylookup id (fun,var) = (fun, map (define id) var)
        define :: Ident -> Var -> Var 
        define id2 var@(id1, (t, def)) = if id1 == id2 then 
                                            (id1, (t, True))
                                         else 
                                            var

checkIterStmtsDecls :: Env -> [IterStmtDecl] -> Type -> Int -> Err Env 
checkIterStmtsDecls env (itr_stmt_decl:itr_stmts_decls) typ pos =
    case itr_stmt_decl of 
        Break _ -> checkIterStmtsDecls env itr_stmts_decls typ pos
        Continue _ -> checkIterStmtsDecls env itr_stmts_decls typ pos
        ItStDe stmt_decl -> checkStmtsDecls env (stmt_decl:[]) typ pos 

getIdLexpr :: LExpr -> Ident 
getIdLexpr lexpr =
    case lexpr of 
        Deref lexpr _ -> getIdLexpr lexpr
        PrePostIncDecr _ _ lexpr _ -> getIdLexpr lexpr 
        BasLExpr blexpr -> getIdBLexpr blexpr

getIdBLexpr :: BLExpr -> Ident 
getIdBLexpr blexpr =
    case blexpr of 
        Id id _ -> id
        ArrayEl blexpr_ _ _ -> getIdBLexpr blexpr_

checkLExpr :: Env -> LExpr -> Err Type 
checkLExpr env lexpr = 
    case lexpr of 
        Lex lexpr p -> checkLExpr env lexpr 
        Deref lexpr p -> 
            case checkLExpr env lexpr of 
                Ok (Pointer typ) ->  Ok typ
                _ -> Bad ("Error : variable " ++ printTree (getIdLexpr lexpr) ++ " at line " ++ show p ++ " isn't declared as a pointer\n")
        PrePostIncDecr _ _ lexpr p -> 
            case checkLExpr env lexpr of 
                Ok T_Int -> Ok T_Int 
                Ok T_Float -> Ok T_Float 
        BasLExpr blexpr -> checkBLExpr env blexpr 
        where 
            checkBLExpr :: Env -> BLExpr -> Err Type
            checkBLExpr env blexpr = 
                case blexpr of 
                    Id id p_ -> 
                        case lookupVar env id of 
                            Just T_Error -> Ok T_Error
                            Just typ -> Ok typ 
                            Nothing ->  Bad ("Error : variable " ++ printTree id ++ " at line " ++ show p_ ++ " is not declared\n")
                    ArrayEl blexpr rexpr p_ -> 
                        case checkRExpr env rexpr of 
                            Ok T_Int -> checkBLExpr env blexpr 
                            _ -> Bad ("Error : incorrect indicization of array " ++ printTree (getIdBLexpr blexpr) ++ " at line " ++ show p_ ++ "\n")

checkRExpr :: Env -> RExpr -> Err Type 
checkRExpr env rexpr = 
    case rexpr of 
        Rexpr rexpr _ -> checkRExpr env rexpr 
        InfixOp infixop rexpr1 rexpr2 pos ->
            do 
                let typ_ = checkRExpr env rexpr1
                let typ__ = checkRExpr env rexpr2
                case checkTypeInfix infixop typ_ typ__ of
                    Just typ -> Ok typ
                    Nothing -> Bad ("Error : operation not permitted between " ++ printTree ( (\(Ok typ) -> typ) typ_ ) ++ " and " ++ printTree ( (\(Ok typ) -> typ) typ__ ) ++ " at line " ++ show pos ++ "\n")
        UnaryOp unaryop rexpr pos -> 
            do
                let typ = checkRExpr env rexpr
                case  checkTypeUnary unaryop typ of 
                    Just typ -> Ok typ
                    Nothing -> Bad ("Error : operation not permitted whit " ++ printTree ( (\(Ok typ_) -> typ_) typ ) ++ " at line " ++ show pos ++ "\n")
        Ref lexpr pos -> 
            case checkLExpr env lexpr of 
                Ok (Pointer typ) -> Ok typ
                Ok _ -> Bad ("Error :  variable " ++ printTree (getIdLexpr lexpr) ++ " used at line " ++ show pos ++ " is not a pointer\n")
        FCall (Call id rexprs pos) -> 
            case lookupFun env id rexprs of
                Just typ -> Ok typ
                Nothing -> Bad ("Error : function used at line " ++ show pos ++ " is not declared\n")
        Lexpr lexpr -> checkLExpr env lexpr
        Int _ -> Ok T_Int
        String _ -> Ok T_String
        Float _ -> Ok T_Float
        Char _ -> Ok T_Char
        Bool _ -> Ok T_Bool 

checkTypeUnary :: UnaryOp -> Err Type -> Maybe Type 
checkTypeUnary unaryop typ@(Ok typ_) = 
    case unaryop of 
        Not -> if (typ == Ok T_Bool) then 
                Just T_Bool
                else 
                Nothing 
        Neg -> if (typ == Ok T_Int || typ == Ok T_Float) then
                Just typ_
               else  
                Nothing 

checkTypeInfix :: InfixOp -> Err Type -> Err Type -> Maybe Type 
checkTypeInfix infixop typ1@(Ok typ1_) typ2@(Ok typ2_) =
    case infixop of 
        ArithOp _  -> if (typ1 == typ2 && (typ1 == Ok T_Int || typ1 == Ok T_Float)) then 
                        Just typ1_
                      else 
                        if ((typ1 == Ok T_Int && typ2 == Ok T_Float) || (typ1 == Ok T_Float && typ2 == Ok T_Int)) then 
                            Just T_Float
                        else 
                            Nothing 
        BoolOp _ -> if (typ1 == typ2 && typ1 == Ok T_Bool) then 
                        Just T_Bool
                    else 
                        Nothing
        RelOp _ -> if (typ1 == typ2 && (typ1 == Ok T_Int || typ1 == Ok T_Float)) then 
                        Just typ1_
                      else 
                        if ((typ1 == Ok T_Int && typ2 == Ok T_Float) || (typ1 == Ok T_Float && typ2 == Ok T_Int)) then 
                            Just T_Float
                        else 
                            Nothing 


checkRExprs :: Env -> [RExpr] -> Err Type
checkRExprs env [rexpr] = checkRExpr env rexpr
checkRExprs env (rexpr:rexprs) =
        case checkRExpr env rexpr of 
            Ok _ -> checkRExprs env rexprs 
            

lookupFun :: Env -> Ident -> [RExpr] -> Maybe Type
lookupFun [] id param = Nothing
lookupFun env@(scope:scopes) id param = 
    case lookup id (fst scope) of
        Nothing -> lookupFun scopes id param
        Just sig -> checkParam env sig param

checkParam :: Env -> (Type, [(Type, Modality)]) -> [RExpr] -> Maybe Type
checkParam env ptyp param = checkP env ( map fst ((\(typ, lpar) -> lpar ) ptyp)) param ((\(typ, lpar) -> typ) ptyp)
    where 
        checkP :: Env -> [Type] -> [RExpr] -> Type -> Maybe Type
        checkP env [] (param:_) typ = Nothing
        checkP env (ptyp:_) [] typ = Nothing
        checkP env [] [] typ = Just typ
        checkP env (ptyp:ptyps) (param:params) typ = 
            if (checkRExpr env param == Ok ptyp) then 
                checkP env ptyps params typ
            else 
                Nothing

lookupVar :: Env -> Ident -> Maybe Type
lookupVar [] id = Nothing 
lookupVar (scope:scopes) id = 
    case lookup id (snd scope) of
        Nothing -> lookupVar scopes id 
        Just var -> if ((snd var) == False) then 
                        Just T_Error
                    else 
                        Just (fst var)

checkType :: Err Type -> Err Type -> Maybe Type 
checkType (Ok typ1) (Ok typ2) = 
    if (typ1 == typ2) then 
        Just typ1
    else 
        if ((typ1 == T_Int && typ2 == T_Float) || (typ1 == T_Float && typ2 == T_Int)) then
            Just T_Float
        else 
            Nothing 