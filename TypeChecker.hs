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
        env1 <- addFun emptyEnv (Ident "writeInt") T_Void [Param (M_Val 0) T_Int (Id (Ident "x") Dollar )] 0
        env2 <- addFun env1 (Ident "writeFloat") T_Void [Param (M_Val 0) T_Float (Id (Ident "x") Dollar )] 0
        env3 <- addFun env2 (Ident "writeChar") T_Void [Param (M_Val 0) T_Char (Id (Ident "x") Dollar )] 0
        env4 <- addFun env3 (Ident "writeString") T_Void [Param (M_Val 0) T_String (Id (Ident "x") Dollar )] 0
        env5 <- addFun env4 (Ident "readInt") T_Int [] 0
        env6 <- addFun env5 (Ident "readFloat") T_Float [] 0
        env7 <- addFun env6 (Ident "readChar") T_Char [] 0
        env8 <- addFun env7 (Ident "readString") T_String [] 0
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
        checkFunDefs env_ decls

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
        checkFunStmts env_ stmts_decls

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
                checkDecls env_ decls
        UndVar typ _ undvardecl ->
            do 
                env_ <- addVars env (map getIdUndVar undvardecl) typ False (map getLineUndVar undvardecl)
                checkDecls env_ decls
        Dfun typ id pos param stmts_decls ->
            do 
                env1 <- addScope env 
                env2 <- addParam env param 
                env3 <- checkFunStmts env2 stmts_decls
                checkStmtsDecls env3 stmts_decls typ pos
                env4 <- remScope env3
                checkDecls env4 decls
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
        addParam :: Env -> [Parameter] -> Err Env 
        addParam env [] = Ok env 
        addParam env (param:params) = 
            case param of 
                (Param mod id typ Dollar) -> addVar env id typ True 0
                (Param mod id typ At) -> addVar env id (Arrdef typ 0) True 0


checkVarInit :: Env -> [VarDeclInit] -> Type -> Err Env 
checkVarInit env [] _ = Ok env
checkVarInit env (vardin:varsdin) typ = 
    case vardin of
        VarDeclInA (VarDeclInitAr id array pos) -> case checkArray env id typ pos array of
                                                     Ok _ -> addVar env id (ArrDef typ 2) True pos
                                                     Bad err -> Bad err 

        VarDeclInV (VarDeclInitV id rexpr pos) -> 
                case checkRExpr env rexpr of
                    Ok typ_ -> 
                        case checkType typ_ typ of
                                Just t -> do 
                                            do 
                                                env_ <- addVar env id typ True pos
                                                checkVarInit env_ varsdin typ
                                Nothing -> Bad ("Error : value assigned to variable " ++ printTree id ++ "declared at line " ++ show pos ++ "should have type" ++ printTree typ
                                       ++ " but has type " ++ printTree typ_  ++ "\n")
                    Bad err -> Bad err
checkArray :: Env -> Ident  -> Type -> Int -> Array -> Err Env 
checkArray env id typ pos array= 
    case array of 
        ArrE rexprs -> 
                case checkRExprs env rexprs of 
                    Ok typ_ ->
                        case checkType typ_ typ of
                            Just t -> Ok env
                            Nothing -> Bad ("Error : while initializing array " ++ printTree id ++ " declared at line " ++ show pos ++ " element's type should be" ++ printTree typ
                                       ++ " but found " ++ printTree typ_ )
                    Bad err -> Bad err
        Arr array _ ->  ((\([Ok env_]) -> Ok env)( map (checkArray env id typ pos) array ))

checkStmtsDecls :: Env -> [StmtDecl] -> Type -> Int -> Err Env 
checkStmtsDecls env [] _ _ = Ok env
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
                        case checkRExpr env rexpr of
                            Ok typ_ ->
                                case checkType typ_ typ of 
                                    Just _ -> Ok env
                                    Nothing -> Bad ("Error : function declared at line " ++ show pos ++ " is not of type " ++ printTree typ ++ " as suggeste ad line " 
                                               ++ show p ++ " by the return statement\n")
                            Bad err -> Bad err
        Iter iterstmt -> 
            case iterstmt of
                While rexpr p stmts_decls -> 
                    do
                        case checkRExpr env rexpr of 
                            Ok T_Bool -> do  
                                            env_ <- addScope env 
                                            env__ <- checkIterStmtsDecls env_ stmts_decls typ pos 
                                            remScope env__
                            _ -> Bad ("Error : invalid guard of while statement at line " ++ show p)
                DoWhile stmts_decls rexpr p -> 
                    case checkRExpr env rexpr of 
                        Ok T_Bool -> do
                                        env_ <- addScope env 
                                        env__ <- checkIterStmtsDecls env stmts_decls typ pos 
                                        remScope env__
                        _ -> Bad ("Error : invalid guard of do-while statement at line " ++ show p)
                DoUntil stmts_decls rexpr p -> 
                    case checkRExpr env rexpr of 
                        Ok T_Bool -> do 
                                        env_ <- addScope env
                                        env__ <- checkIterStmtsDecls env stmts_decls typ pos
                                        remScope env__ 
                        _ -> Bad ("Error : invalid guard of do-until statement at line " ++ show p)
                ForEach forstmt forstmt_ p stmts_decls ->
                    do 
                        env_ <- addScope env
                        case forstmt of 
                            ForDecl typ_ id p_ ->
                                do 
                                    env__ <- addVar env_ id typ_ True pos
                                    case forstmt_ of 
                                        LexprForStmt lexpr ->
                                            case checkLExpr env__ lexpr of 
                                                Ok (ArrDef typ__ _) ->
                                                    case checkType typ_ typ__ of 
                                                        Just _ -> do
                                                                    env___ <- checkIterStmtsDecls env stmts_decls typ pos
                                                                    remScope env___
                                                        Nothing -> Bad ("Error : in for each statement at line " ++ show p_ ++ " variable " ++ printTree id ++ "(" ++ printTree typ_ ++ ")" 
                                                                    ++ " is not of the same type of var " ++ printTree id ++ "(" ++ printTree typ__ ++ ")\n" ) 
                                                Ok _ -> Bad("Error : in for each statement at line " ++ show p_ ++ " iterable shold be and array\n")
                                                _ -> Bad("Error : in for statement at line " ++ show p_ ++ " iterable not correctly defined\n")
                                        _ -> Bad("Error : in for statement at line " ++ show p_ ++ " iterable not correctly defined\n")
                            _ -> Bad ("Error : invalid guard in for each statement at line " ++ show p ++ "\n")
                -- For  forstmtdecl rexpr forstmt p stmts_decls -> checkForStmt env forstmtdecl rexpr forstmt p stmts_decls                
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
                {- funzione definita, ma non inizializzata -} 
                Ok T_Error  -> 
                    case ass of 
                        Assign _ -> 
                            do
                                env_ <- signAsDef env (getIdLexpr lexpr)
                                checkStmt env stmt typ pos
                Ok typ_  ->     
                        case checkRExpr env rexpr of 
                            Ok typ__ ->
                                case checkType typ_ typ__ of 
                                    Just _ -> Ok env 
                                    Nothing -> Bad ("Error : bad typing at line " ++ show p ++ " in assignement of var " ++ printTree  (getIdLexpr lexpr)
                                              ++ " of typ " ++ printTree typ_ ++ "\n")
                            Bad err -> Bad err
             {- operazioni infisse -}
        TryC (Try _ stmts_decls typ _ p stmts_decls_) ->
            do 
                env_ <- addScope env
                env__ <- checkStmtsDecls env_ stmts_decls typ pos 
                case typ of
                    T_Error -> do
                                env___ <- checkStmtsDecls env__ stmts_decls_ typ pos
                                remScope env___
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
checkIterStmtsDecls env [] _ _ = Ok env
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
                _ -> Bad ("Error\n")
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
        InfixOp infixop rexpr1 rexpr2 pos -> case checkRExpr env rexpr1 of 
                                                Ok typ_ -> case checkRExpr env rexpr2 of
                                                            Ok typ__ -> case checkTypeInfix infixop typ_ typ__ of
                                                                        Just typ -> Ok typ
                                                                        Nothing -> Bad ("Error : operation not permitted between " ++ printTree  typ_  ++ " and " ++ printTree typ__  ++ " at line " ++ show pos ++ "\n")
                                                            Bad err -> Bad err
                                                Bad err -> Bad err        
        UnaryOp unaryop rexpr pos -> 
            case checkRExpr env rexpr of 
                Ok typ -> case  checkTypeUnary unaryop typ of 
                            Just typ -> Ok typ
                            Nothing -> Bad ("Error : operation not permitted whit " ++ printTree typ  ++ " at line " ++ show pos ++ "\n")
                Bad err -> Bad err
                
        Ref lexpr pos -> 
            case checkLExpr env lexpr of 
                Ok (Pointer typ) -> Ok typ
                Ok _ -> Bad ("Error :  variable " ++ printTree (getIdLexpr lexpr) ++ " used at line " ++ show pos ++ " is not a pointer\n")
        FCall (Call id rexprs pos) -> 
            case lookupFun env id rexprs of
                Just typ -> Ok typ
                Nothing -> Bad ("Error : function used at line " ++ show pos ++ " is not declared\n")
        Lexpr lexpr -> checkLExpr env lexpr
        Const const -> case const of
                        Int _ -> Ok T_Int
                        String _ -> Ok T_String
                        Float _ -> Ok T_Float
                        Char _ -> Ok T_Char
                        Bool _ -> Ok T_Bool 

checkTypeUnary :: UnaryOp -> Type -> Maybe Type 
checkTypeUnary unaryop typ = 
    case unaryop of 
        Not -> case (typ == T_Bool) of
                True -> Just T_Bool
                False -> Nothing 
        Neg -> case (typ == T_Int || typ == T_Float) of
                True -> Just typ
                False -> Nothing
 
checkTypeInfix :: InfixOp -> Type -> Type -> Maybe Type 
checkTypeInfix infixop typ1 typ2 =
    case infixop of 
        ArithOp _  -> case (typ1 == typ2 && (typ1 == T_Int || typ1 == T_Float)) of 
                        True -> Just typ1 
                        False -> case ((typ1 == T_Int && typ2 == T_Float) || (typ1 == T_Float && typ2 == T_Int)) of
                                    True -> Just T_Float
        BoolOp _ -> case (typ1 == typ2 && typ1 == T_Bool) of 
                        True -> Just T_Bool
                        False -> Nothing
        RelOp _ -> case (typ1 == typ2 && (typ1 == T_Int || typ1 == T_Float)) of 
                        True -> Just T_Bool
                        False -> case ((typ1 == T_Int && typ2 == T_Float) || (typ1 == T_Float && typ2 == T_Int)) of
                                    True -> Just T_Bool
                                    False -> Nothing 

checkRExprs :: Env -> [RExpr] -> Err Type
checkRExprs env [rexpr] = checkRExpr env rexpr
checkRExprs env (rexpr:rexprs) =
        case checkRExpr env rexpr of 
            Ok _ -> checkRExprs env rexprs 
            

lookupFun :: Env -> Ident -> [RExpr] -> Type -> Maybe Type
lookupFun [] id param = Nothing
lookupFun env@(scope:scopes) id param = 
    case lookup id (fst scope) of
        Nothing -> lookupFun scopes id param
        Just sig -> checkParam env (snd . snd sig) param (fst . snd sig)

checkParam :: Env -> [(Type, Modality)] -> [RExpr] -> Type -> Maybe Type
checkParam _ [] [] typ = Just typ
checkParam _ [] _ _ = Nothing
checkParam _  _ [] _ = Nothing
checkParam env (param:params) (rexpr:rexprs) typ = 
    case snd param of
        M_Const _ -> case rexpr of
                        Const -> case checkRExprs env rexpr of 
                                    Ok typ_ -> case checkType typ_ (fst param) of 
                                                Just _ -> checkParam env params rexprs typ 
                                                Nothing -> Nothing
                                    _ -> Nothing
                        _ -> Nothing 
        M_Val _ -> case checkRExpr env rexpr of 
                        Ok typ_ -> case checkType typ_ (fst . param) of 
                                    Just _ -> checkParam env params rexpr typ 
                                    Nothing -> Nothing 
                        _ -> Nothing

lookupVar :: Env -> Ident -> Maybe Type
lookupVar [] id = Nothing 
lookupVar (scope:scopes) id = 
    case lookup id (snd scope) of
        Nothing -> lookupVar scopes id 
        Just var -> case snd var of
                       False -> Just T_Error
                       True -> Just (fst var)


checkType :: Type -> Type -> Maybe Type 
checkType typ1 typ2 = 
    case (typ1 == typ2) of 
        True -> Just typ1
        False ->
            case ((typ1 == T_Int && typ2 == T_Float) || (typ1 == T_Float && typ2 == T_Int)) of
                True -> Just T_Float
                False -> case typ1 of
                            ArrDef typ _ -> checkType typ typ2
                            _ -> case typ2 of 
                                     ArrDef typ _ -> checkType typ typ1 
                                     _ -> Nothing


