{-# OPTIONS_GHC -w #-}
{-# OPTIONS -fglasgow-exts -cpp #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParPerl where
import AbsPerl
import LexPerl
import ErrM
import qualified Data.Array as Happy_Data_Array
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.5

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
happyIn7 :: (Integer) -> (HappyAbsSyn )
happyIn7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn7 #-}
happyOut7 :: (HappyAbsSyn ) -> (Integer)
happyOut7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut7 #-}
happyIn8 :: (Char) -> (HappyAbsSyn )
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn ) -> (Char)
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
happyIn9 :: (String) -> (HappyAbsSyn )
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn ) -> (String)
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
happyIn10 :: (Double) -> (HappyAbsSyn )
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> (Double)
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
happyIn11 :: (Ident) -> (HappyAbsSyn )
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> (Ident)
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyIn12 :: (Boolean) -> (HappyAbsSyn )
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn ) -> (Boolean)
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
happyIn13 :: (RExpr) -> (HappyAbsSyn )
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> (RExpr)
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
happyIn14 :: (FunCall) -> (HappyAbsSyn )
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> (FunCall)
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
happyIn15 :: ([RExpr]) -> (HappyAbsSyn )
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> ([RExpr])
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
happyIn16 :: (LExpr) -> (HappyAbsSyn )
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn ) -> (LExpr)
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
happyIn17 :: (LExpr) -> (HappyAbsSyn )
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn ) -> (LExpr)
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
happyIn18 :: (LExpr) -> (HappyAbsSyn )
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> (LExpr)
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
happyIn19 :: (BLExpr) -> (HappyAbsSyn )
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> (BLExpr)
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyIn20 :: (Program) -> (HappyAbsSyn )
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn ) -> (Program)
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
happyIn21 :: ([Decl]) -> (HappyAbsSyn )
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn ) -> ([Decl])
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
happyIn22 :: (Decl) -> (HappyAbsSyn )
happyIn22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn ) -> (Decl)
happyOut22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut22 #-}
happyIn23 :: ([VarDeclInit]) -> (HappyAbsSyn )
happyIn23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn ) -> ([VarDeclInit])
happyOut23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut23 #-}
happyIn24 :: ([UndVarDecl]) -> (HappyAbsSyn )
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> ([UndVarDecl])
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyIn25 :: (UndVarDecl) -> (HappyAbsSyn )
happyIn25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn25 #-}
happyOut25 :: (HappyAbsSyn ) -> (UndVarDecl)
happyOut25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut25 #-}
happyIn26 :: (UndArr) -> (HappyAbsSyn )
happyIn26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn26 #-}
happyOut26 :: (HappyAbsSyn ) -> (UndArr)
happyOut26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut26 #-}
happyIn27 :: (UndVar) -> (HappyAbsSyn )
happyIn27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn27 #-}
happyOut27 :: (HappyAbsSyn ) -> (UndVar)
happyOut27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut27 #-}
happyIn28 :: (Type) -> (HappyAbsSyn )
happyIn28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn28 #-}
happyOut28 :: (HappyAbsSyn ) -> (Type)
happyOut28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut28 #-}
happyIn29 :: (VarDeclInit) -> (HappyAbsSyn )
happyIn29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn29 #-}
happyOut29 :: (HappyAbsSyn ) -> (VarDeclInit)
happyOut29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut29 #-}
happyIn30 :: (VarDeclInitArray) -> (HappyAbsSyn )
happyIn30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn30 #-}
happyOut30 :: (HappyAbsSyn ) -> (VarDeclInitArray)
happyOut30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut30 #-}
happyIn31 :: (VarDeclInitVar) -> (HappyAbsSyn )
happyIn31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn31 #-}
happyOut31 :: (HappyAbsSyn ) -> (VarDeclInitVar)
happyOut31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut31 #-}
happyIn32 :: ([Array]) -> (HappyAbsSyn )
happyIn32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn32 #-}
happyOut32 :: (HappyAbsSyn ) -> ([Array])
happyOut32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut32 #-}
happyIn33 :: (Array) -> (HappyAbsSyn )
happyIn33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn33 #-}
happyOut33 :: (HappyAbsSyn ) -> (Array)
happyOut33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut33 #-}
happyIn34 :: ([Parameter]) -> (HappyAbsSyn )
happyIn34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn34 #-}
happyOut34 :: (HappyAbsSyn ) -> ([Parameter])
happyOut34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut34 #-}
happyIn35 :: (Parameter) -> (HappyAbsSyn )
happyIn35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn35 #-}
happyOut35 :: (HappyAbsSyn ) -> (Parameter)
happyOut35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut35 #-}
happyIn36 :: (Modality) -> (HappyAbsSyn )
happyIn36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn36 #-}
happyOut36 :: (HappyAbsSyn ) -> (Modality)
happyOut36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut36 #-}
happyIn37 :: ([StmtDecl]) -> (HappyAbsSyn )
happyIn37 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn37 #-}
happyOut37 :: (HappyAbsSyn ) -> ([StmtDecl])
happyOut37 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut37 #-}
happyIn38 :: (StmtDecl) -> (HappyAbsSyn )
happyIn38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn38 #-}
happyOut38 :: (HappyAbsSyn ) -> (StmtDecl)
happyOut38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut38 #-}
happyIn39 :: (Stmt) -> (HappyAbsSyn )
happyIn39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn39 #-}
happyOut39 :: (HappyAbsSyn ) -> (Stmt)
happyOut39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut39 #-}
happyIn40 :: (Assignment_op) -> (HappyAbsSyn )
happyIn40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn40 #-}
happyOut40 :: (HappyAbsSyn ) -> (Assignment_op)
happyOut40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut40 #-}
happyIn41 :: (TryCatch) -> (HappyAbsSyn )
happyIn41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn41 #-}
happyOut41 :: (HappyAbsSyn ) -> (TryCatch)
happyOut41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut41 #-}
happyIn42 :: (JumpStmt) -> (HappyAbsSyn )
happyIn42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn42 #-}
happyOut42 :: (HappyAbsSyn ) -> (JumpStmt)
happyOut42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut42 #-}
happyIn43 :: (SelectionStmt) -> (HappyAbsSyn )
happyIn43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn43 #-}
happyOut43 :: (HappyAbsSyn ) -> (SelectionStmt)
happyOut43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut43 #-}
happyIn44 :: (Elsif) -> (HappyAbsSyn )
happyIn44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn44 #-}
happyOut44 :: (HappyAbsSyn ) -> (Elsif)
happyOut44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut44 #-}
happyIn45 :: (IterStmt) -> (HappyAbsSyn )
happyIn45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn45 #-}
happyOut45 :: (HappyAbsSyn ) -> (IterStmt)
happyOut45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut45 #-}
happyIn46 :: (ForStmtDecl) -> (HappyAbsSyn )
happyIn46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn46 #-}
happyOut46 :: (HappyAbsSyn ) -> (ForStmtDecl)
happyOut46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut46 #-}
happyIn47 :: (ForStmt) -> (HappyAbsSyn )
happyIn47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn47 #-}
happyOut47 :: (HappyAbsSyn ) -> (ForStmt)
happyOut47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut47 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x00\x00\x7b\x00\xa1\x00\x78\x00\x57\x01\x00\x00\x4f\x01\x00\x00\x29\x00\x6d\x01\x58\x00\x78\x00\x37\x00\x37\x00\x48\x01\x00\x00\x00\x00\x00\x00\x00\x00\x82\x01\x00\x00\x77\x00\x00\x00\x00\x00\x57\x00\x57\x00\x57\x00\x00\x00\x00\x00\x78\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7b\x01\x96\x03\x4d\x01\x00\x00\x72\x01\x00\x00\x00\x00\x00\x00\x00\x00\x4c\x01\x80\x01\x26\x00\x79\x01\x78\x01\x3c\x01\x71\x01\x00\x00\x2e\x01\xde\xff\x00\x00\x08\x02\x08\x02\x0e\x02\x57\x00\x00\x00\x57\x00\x57\x00\x02\x01\x00\x00\x6b\x01\x08\x02\xfe\xff\x00\x00\x00\x00\x57\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x70\x03\x68\x01\x5e\x04\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x57\x00\x00\x00\x00\x00\x28\x01\x00\x00\x64\x01\x00\x00\x00\x00\x57\x00\x00\x00\x00\x00\x4d\x03\x00\x00\x31\x03\x62\x01\x0a\x04\x49\x04\x49\x04\x49\x04\x49\x04\x49\x04\x52\x01\xa3\x00\xa3\x00\x52\x01\x52\x01\x34\x04\x52\x01\x1f\x04\x00\x00\x14\x03\xef\x01\x53\x01\x21\x01\x08\x02\x12\x00\x00\x00\x78\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x26\x00\x57\x00\xf8\x02\xda\x02\xd0\x01\xbe\x02\x00\x00\x00\x00\x00\x00\x00\x00\xea\xff\x15\x00\x4b\x01\x4a\x01\x49\x01\x00\x00\x00\x00\x47\x01\x00\x00\x00\x00\x0a\x01\x0a\x01\x10\x01\x46\x01\x11\x01\x25\x01\x00\x00\xfe\x00\x8c\x03\x41\x01\x00\x00\x03\x01\x04\x00\x02\x01\x57\x00\xdb\xff\x00\x00\x00\x00\x57\x00\x00\x00\x00\x00\x33\x01\x31\x01\xc3\x00\x57\x00\xfa\x00\x00\x00\xf5\x00\x00\x00\x2a\x01\x00\x00\xd5\x03\x0f\x01\x15\x01\x13\x01\x18\x00\x05\x00\x00\x00\x00\x00\x00\x00\xe4\x00\xe4\x00\x00\x00\xe4\x00\xe4\x00\x57\x00\x23\x01\x00\x00\x1b\x01\x12\x01\x08\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb1\x01\x08\x02\x92\x01\x00\x00\x02\x01\x8c\x03\x26\x00\x57\x00\x57\x00\xa0\x02\x84\x02\x17\x01\x57\x00\x73\x01\xe2\xff\xe1\xff\x00\x00\xea\xff\xd5\x03\xdf\x00\x1d\x00\x8c\x03\x01\x01\x00\x01\x00\x00\x00\x00\x00\x00\x0e\x01\x01\x00\x00\x00\x00\x00\x00\x00\x0b\x01\x00\x00\xd3\x00\x08\x01\x00\x00\x8c\x03\xd1\x00\xf4\x00\xf1\x00\x00\x00\x00\x00\x00\x00\x0a\x00\x00\x00\xcd\x00\x54\x01\x4a\x02\xf3\x00\xe5\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x35\x01\x66\x02\x16\x01\x00\x00\xb9\x00\x00\x00\xf7\x00\x00\x00\x00\x00\x00\x00\xc4\x00\xe2\xff\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\xf8\xff\xe2\x03\x60\x06\x84\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x68\x00\x80\x04\xf6\x00\xb2\x00\xe0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x53\x06\x46\x06\x39\x06\x00\x00\x00\x00\xca\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd7\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb7\x03\x00\x00\x00\x00\x00\x00\x00\x00\xc5\x00\x00\x00\xd2\x00\x00\x00\xc8\x00\xc1\x00\xc1\x03\x2c\x06\xb6\x00\x1f\x06\x12\x06\xb8\x00\x00\x00\x00\x00\xbd\x00\xa9\x00\x98\x00\x00\x00\x05\x06\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf8\x05\xeb\x05\xde\x05\xd1\x05\xc4\x05\xb7\x05\xaa\x05\x9d\x05\x90\x05\x83\x05\x76\x05\x69\x05\x5c\x05\x4f\x05\xcd\x04\x00\x00\x00\x00\xcb\x00\x00\x00\x00\x00\x00\x00\x00\x00\x42\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc1\x03\x00\x00\xc7\x00\xb5\x00\x00\x00\x00\x00\x62\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb3\x03\x35\x05\x00\x00\x00\x00\xc1\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc2\x00\xdf\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb3\x00\xad\x00\xa7\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xab\x00\x00\x00\x82\x00\x28\x05\x00\x00\x00\x00\x00\x00\xbf\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x05\x96\x00\x00\x00\x00\x00\x7a\x00\x00\x00\x79\x00\xd5\x00\x00\x00\x00\x00\x00\x00\x46\x00\x39\x00\x00\x00\x00\x00\x00\x00\x91\x00\x8d\x00\x00\x00\x89\x00\x84\x00\x0e\x05\x00\x00\x00\x00\x00\x00\x00\x00\x71\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc1\x03\x6f\x00\xc1\x03\x61\x00\x4e\x00\x00\x00\xaa\x03\x01\x05\xf4\x04\x00\x00\x00\x00\x00\x00\xe7\x04\xc1\x03\x4b\x00\x6b\x00\x00\x00\x53\x00\xd0\x00\x00\x00\xb2\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x97\x04\x4a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x36\x00\xda\x04\x35\x00\x00\x00\xc1\x03\x00\x00\x00\x00\x00\x00\x00\x00\x7c\x04\x00\x00\x00\x00\x25\x00\xc1\x03\x00\x00\xc1\x03\x00\x00\x00\x00\x00\x00\xc1\x03\x00\x00\x00\x00\x24\x00\xc1\x03\x1c\x00\x00\x00\x00\x00"#

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\xca\xff\x00\x00\x00\x00\x00\x00\x00\x00\xfb\xff\x00\x00\xd7\xff\xd3\xff\xcf\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe0\xff\xdf\xff\xde\xff\xdd\xff\x00\x00\xdc\xff\x00\x00\xe1\xff\xe2\xff\x00\x00\x00\x00\x00\x00\xf5\xff\xf6\xff\x00\x00\xfa\xff\xf9\xff\xf8\xff\xf7\xff\x00\x00\x00\x00\x00\x00\x97\xff\x00\x00\x98\xff\x99\xff\x8b\xff\x8a\xff\x00\x00\x00\x00\x00\x00\x00\x00\x89\xff\x00\x00\x00\x00\xa0\xff\x00\x00\xcb\xff\xc9\xff\x00\x00\x00\x00\x00\x00\x00\x00\xa0\xff\x00\x00\x00\x00\x00\x00\x7c\xff\x00\x00\x00\x00\x00\x00\xa0\xff\x9a\xff\x00\x00\x8e\xff\x8f\xff\x93\xff\x92\xff\x90\xff\x91\xff\x95\xff\x94\xff\x8d\xff\x9c\xff\xe3\xff\xe4\xff\x00\x00\xe2\xff\xe5\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xda\xff\xcc\xff\xd4\xff\x00\x00\xd5\xff\x00\x00\xcd\xff\xd6\xff\x00\x00\xd2\xff\xd1\xff\x00\x00\xd0\xff\xd9\xff\x00\x00\xf3\xff\xec\xff\xed\xff\xf1\xff\xee\xff\xef\xff\xe8\xff\xea\xff\xeb\xff\xe6\xff\xe9\xff\xf2\xff\xe7\xff\xf0\xff\xf4\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb5\xff\x00\x00\xbb\xff\xba\xff\xb9\xff\xb8\xff\xb6\xff\xb7\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x9e\xff\x9f\xff\x9d\xff\x9b\xff\x00\x00\x00\x00\x00\x00\x00\x00\xc3\xff\xc1\xff\xc0\xff\xc5\xff\xb4\xff\xb3\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x88\xff\x00\x00\x7a\xff\x00\x00\xbc\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x96\xff\xdb\xff\xda\xff\xce\xff\xd8\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7b\xff\x00\x00\xa0\xff\x00\x00\xa0\xff\xab\xff\x00\x00\xbf\xff\xbe\xff\x00\x00\x00\x00\xc7\xff\xc8\xff\xc2\xff\x00\x00\x00\x00\xc4\xff\x00\x00\x00\x00\x00\x00\x00\x00\xbd\xff\x00\x00\xaa\xff\x00\x00\xa4\xff\xa1\xff\xa5\xff\xa3\xff\xa6\xff\xa2\xff\x00\x00\x00\x00\x00\x00\xa0\xff\x00\x00\x7d\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x87\xff\x00\x00\x83\xff\x00\x00\xab\xff\x00\x00\xda\xff\xb1\xff\x00\x00\x00\x00\xbf\xff\xbe\xff\xac\xff\x00\x00\xda\xff\xa0\xff\xa9\xff\xa8\xff\x00\x00\x86\xff\x00\x00\x00\x00\x7f\xff\x7e\xff\x00\x00\x00\x00\x00\x00\x81\xff\x82\xff\xa0\xff\x00\x00\xa0\xff\x00\x00\x00\x00\x00\x00\x00\x00\xaf\xff\xb2\xff\xda\xff\xad\xff\xc6\xff\xa0\xff\x00\x00\x00\x00\x00\x00\x80\xff\x00\x00\x84\xff\x00\x00\xae\xff\x8c\xff\xa0\xff\x00\x00\x00\x00\x85\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x03\x00\x01\x00\x22\x00\x03\x00\x0d\x00\x0e\x00\x03\x00\x03\x00\x08\x00\x09\x00\x01\x00\x22\x00\x03\x00\x2c\x00\x2d\x00\x0f\x00\x33\x00\x08\x00\x12\x00\x13\x00\x03\x00\x3b\x00\x39\x00\x03\x00\x0f\x00\x3f\x00\x03\x00\x12\x00\x13\x00\x01\x00\x1e\x00\x03\x00\x20\x00\x21\x00\x1e\x00\x23\x00\x08\x00\x22\x00\x46\x00\x1e\x00\x03\x00\x20\x00\x21\x00\x0f\x00\x23\x00\x08\x00\x12\x00\x13\x00\x33\x00\x48\x00\x1e\x00\x22\x00\x0f\x00\x1e\x00\x22\x00\x0f\x00\x13\x00\x03\x00\x1e\x00\x13\x00\x20\x00\x21\x00\x08\x00\x23\x00\x25\x00\x1e\x00\x1e\x00\x1e\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x11\x00\x12\x00\x13\x00\x14\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x1e\x00\x1e\x00\x1e\x00\x10\x00\x04\x00\x01\x00\x33\x00\x03\x00\x03\x00\x16\x00\x17\x00\x18\x00\x08\x00\x08\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x0f\x00\x0f\x00\x1e\x00\x12\x00\x13\x00\x13\x00\x04\x00\x02\x00\x48\x00\x21\x00\x25\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x1e\x00\x1e\x00\x20\x00\x21\x00\x02\x00\x23\x00\x03\x00\x05\x00\x06\x00\x03\x00\x1e\x00\x08\x00\x0a\x00\x0b\x00\x08\x00\x15\x00\x0e\x00\x15\x00\x0f\x00\x04\x00\x12\x00\x0f\x00\x13\x00\x15\x00\x04\x00\x13\x00\x18\x00\x19\x00\x04\x00\x1b\x00\x1c\x00\x1d\x00\x04\x00\x1e\x00\x1e\x00\x1e\x00\x1e\x00\x04\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x48\x00\x26\x00\x01\x00\x21\x00\x03\x00\x2a\x00\x2b\x00\x00\x00\x05\x00\x08\x00\x2f\x00\x30\x00\x31\x00\x0a\x00\x0b\x00\x04\x00\x0f\x00\x04\x00\x37\x00\x12\x00\x13\x00\x3a\x00\x1e\x00\x04\x00\x15\x00\x42\x00\x3f\x00\x40\x00\x0a\x00\x0b\x00\x0c\x00\x1e\x00\x49\x00\x20\x00\x21\x00\x48\x00\x23\x00\x02\x00\x04\x00\x03\x00\x05\x00\x06\x00\x15\x00\x04\x00\x08\x00\x0a\x00\x0b\x00\x04\x00\x27\x00\x0e\x00\x15\x00\x0f\x00\x1e\x00\x12\x00\x15\x00\x13\x00\x15\x00\x21\x00\x17\x00\x18\x00\x19\x00\x15\x00\x1b\x00\x1c\x00\x1d\x00\x0f\x00\x1e\x00\x1e\x00\x04\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x26\x00\x1b\x00\x1c\x00\x1d\x00\x2a\x00\x2b\x00\x1b\x00\x1c\x00\x1d\x00\x2f\x00\x30\x00\x31\x00\x11\x00\x33\x00\x21\x00\x40\x00\x03\x00\x37\x00\x09\x00\x39\x00\x3a\x00\x08\x00\x0a\x00\x0b\x00\x0c\x00\x3f\x00\x40\x00\x42\x00\x0f\x00\x43\x00\x17\x00\x07\x00\x13\x00\x17\x00\x48\x00\x40\x00\x0c\x00\x0d\x00\x08\x00\x40\x00\x10\x00\x40\x00\x09\x00\x1e\x00\x14\x00\x09\x00\x16\x00\x03\x00\x1a\x00\x1a\x00\x1a\x00\x26\x00\x08\x00\x40\x00\x09\x00\x2a\x00\x2b\x00\x11\x00\x09\x00\x0f\x00\x2f\x00\x30\x00\x31\x00\x13\x00\x33\x00\x08\x00\x48\x00\x1a\x00\x37\x00\x1a\x00\x39\x00\x3a\x00\x08\x00\x24\x00\x1e\x00\x40\x00\x3f\x00\x40\x00\x03\x00\x08\x00\x43\x00\x08\x00\x26\x00\x08\x00\x40\x00\x48\x00\x2a\x00\x2b\x00\x48\x00\x41\x00\x0f\x00\x2f\x00\x30\x00\x31\x00\x13\x00\x33\x00\x09\x00\x48\x00\x27\x00\x37\x00\x08\x00\x39\x00\x3a\x00\x40\x00\x48\x00\x1e\x00\x44\x00\x3f\x00\x40\x00\x03\x00\x11\x00\x43\x00\x11\x00\x26\x00\x08\x00\x0b\x00\x48\x00\x2a\x00\x2b\x00\x17\x00\x17\x00\x0f\x00\x2f\x00\x30\x00\x31\x00\x13\x00\x33\x00\x48\x00\x17\x00\x09\x00\x37\x00\x09\x00\x39\x00\x3a\x00\x48\x00\x09\x00\x1e\x00\x08\x00\x3f\x00\x40\x00\x03\x00\x49\x00\x43\x00\x08\x00\x26\x00\x08\x00\x40\x00\x48\x00\x2a\x00\x2b\x00\x08\x00\x08\x00\x0f\x00\x2f\x00\x30\x00\x31\x00\x13\x00\x33\x00\x08\x00\x17\x00\x08\x00\x37\x00\x40\x00\x39\x00\x3a\x00\x22\x00\x48\x00\x1e\x00\x17\x00\x3f\x00\x40\x00\x03\x00\x49\x00\x43\x00\x49\x00\x26\x00\x08\x00\x44\x00\x48\x00\x2a\x00\x2b\x00\xff\xff\xff\xff\x0f\x00\x2f\x00\x30\x00\x31\x00\x13\x00\x33\x00\xff\xff\xff\xff\xff\xff\x37\x00\xff\xff\x39\x00\x3a\x00\xff\xff\xff\xff\x1e\x00\xff\xff\x3f\x00\x40\x00\x03\x00\xff\xff\x43\x00\xff\xff\x26\x00\x08\x00\xff\xff\x48\x00\x2a\x00\x2b\x00\xff\xff\xff\xff\x0f\x00\x2f\x00\x30\x00\x31\x00\x13\x00\x33\x00\xff\xff\xff\xff\xff\xff\x37\x00\xff\xff\x39\x00\x3a\x00\xff\xff\xff\xff\x1e\x00\xff\xff\x3f\x00\x40\x00\x03\x00\xff\xff\x43\x00\xff\xff\x26\x00\x08\x00\xff\xff\x48\x00\x2a\x00\x2b\x00\xff\xff\xff\xff\x0f\x00\x2f\x00\x30\x00\x31\x00\x13\x00\x33\x00\xff\xff\xff\xff\xff\xff\x37\x00\xff\xff\x39\x00\x3a\x00\xff\xff\xff\xff\x1e\x00\xff\xff\x3f\x00\x40\x00\x03\x00\xff\xff\x43\x00\xff\xff\x26\x00\x08\x00\xff\xff\x48\x00\x2a\x00\x2b\x00\xff\xff\xff\xff\x0f\x00\x2f\x00\x30\x00\x31\x00\x13\x00\x33\x00\xff\xff\xff\xff\xff\xff\x37\x00\xff\xff\x39\x00\x3a\x00\xff\xff\xff\xff\x1e\x00\xff\xff\x3f\x00\x40\x00\x03\x00\xff\xff\x43\x00\xff\xff\x26\x00\x08\x00\xff\xff\x48\x00\x2a\x00\x2b\x00\xff\xff\xff\xff\x0f\x00\x2f\x00\x30\x00\x31\x00\x13\x00\x33\x00\xff\xff\xff\xff\xff\xff\x37\x00\x1f\x00\x39\x00\x3a\x00\xff\xff\x23\x00\x1e\x00\x25\x00\x3f\x00\x40\x00\x28\x00\xff\xff\x43\x00\xff\xff\x26\x00\xff\xff\x2e\x00\x48\x00\x2a\x00\x2b\x00\x32\x00\xff\xff\xff\xff\x2f\x00\x30\x00\x31\x00\x38\x00\x33\x00\xff\xff\xff\xff\xff\xff\x37\x00\x3e\x00\x39\x00\x3a\x00\xff\xff\xff\xff\xff\xff\x02\x00\x3f\x00\x40\x00\x05\x00\x06\x00\x43\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x48\x00\xff\xff\x0e\x00\xff\xff\xff\xff\x11\x00\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\xff\xff\x09\x00\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\xff\xff\xff\xff\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\x42\x00\x09\x00\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\x42\x00\x09\x00\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\xff\xff\xff\xff\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\x42\x00\x09\x00\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\x42\x00\x09\x00\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\xff\xff\xff\xff\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\x42\x00\x09\x00\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\x42\x00\xff\xff\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\x17\x00\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\xff\xff\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\xff\xff\x42\x00\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\x11\x00\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\xff\xff\x42\x00\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\xff\xff\xff\xff\x24\x00\x02\x00\x42\x00\xff\xff\x05\x00\x06\x00\xff\xff\xff\xff\x09\x00\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\x02\x00\x42\x00\xff\xff\x05\x00\x06\x00\xff\xff\xff\xff\xff\xff\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\x07\x00\x12\x00\xff\xff\xff\xff\x15\x00\x0c\x00\x0d\x00\x18\x00\x19\x00\x10\x00\x1b\x00\x1c\x00\x1d\x00\x14\x00\xff\xff\x16\x00\x17\x00\x04\x00\xff\xff\x1a\x00\xff\xff\x42\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x04\x00\xff\xff\xff\xff\xff\xff\x04\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\xff\xff\x04\x00\xff\xff\xff\xff\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x42\x00\xff\xff\x0f\x00\xff\xff\x28\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x41\x00\xff\xff\xff\xff\xff\xff\x28\x00\xff\xff\xff\xff\xff\xff\x28\x00\x1f\x00\x20\x00\xff\xff\x22\x00\x23\x00\x24\x00\x04\x00\x26\x00\xff\xff\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x1f\x00\x16\x00\x17\x00\x18\x00\x23\x00\xff\xff\x25\x00\xff\xff\xff\xff\x28\x00\x29\x00\xff\xff\xff\xff\xff\xff\x20\x00\x2e\x00\x22\x00\x23\x00\x24\x00\x32\x00\x26\x00\x34\x00\x35\x00\x36\x00\x02\x00\x38\x00\xff\xff\x05\x00\x06\x00\x3c\x00\x3d\x00\x3e\x00\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\x02\x00\x18\x00\x19\x00\x05\x00\x1b\x00\x1c\x00\x1d\x00\xff\xff\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\x02\x00\x18\x00\x19\x00\x05\x00\x1b\x00\x1c\x00\x1d\x00\xff\xff\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\x02\x00\x18\x00\x19\x00\x05\x00\x1b\x00\x1c\x00\x1d\x00\xff\xff\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\x02\x00\x18\x00\x19\x00\x05\x00\x1b\x00\x1c\x00\x1d\x00\xff\xff\x0a\x00\x0b\x00\xff\xff\xff\xff\x0e\x00\xff\xff\xff\xff\xff\xff\x12\x00\xff\xff\xff\xff\x15\x00\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\x1b\x00\x1c\x00\x1d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\xff\xff\xff\xff\xff\xff\xff\xff\x19\x00\x1a\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x19\x00\x1a\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x1a\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\x07\x00\xff\xff\x09\x00\x0a\x00\x0b\x00\x0c\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x84\x00\x19\x00\xa5\x00\x0b\x00\x33\x00\x34\x00\xbc\x00\xcb\x00\xf8\x00\xb0\xff\x19\x00\xa5\x00\x0b\x00\xfe\x00\xff\x00\x0d\x00\x37\x00\x1a\x00\x1b\x00\x0e\x00\xae\x00\xb8\x00\x38\x00\xa3\x00\x0d\x00\xb9\x00\xce\x00\x1b\x00\x0e\x00\x19\x00\x0f\x00\x0b\x00\x1c\x00\x1d\x00\xcc\x00\x1e\x00\xf8\x00\xa5\x00\x20\x00\x0f\x00\x0b\x00\x1c\x00\x1d\x00\x0d\x00\x1e\x00\x0c\x00\x1b\x00\x0e\x00\x85\x00\x22\x00\xa4\x00\xa5\x00\x0d\x00\xcf\x00\xa5\x00\x6c\x00\x0e\x00\x66\x00\x0f\x00\x6d\x00\x1c\x00\x1d\x00\x0c\x00\x1e\x00\x1f\x01\x1d\x01\x19\x01\x0f\x00\x06\x00\x1f\x00\x20\x00\x21\x00\x22\x00\xc9\x00\x9c\x00\x9d\x00\x9e\x00\x06\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x13\x01\x15\x01\x0f\x00\xcc\x00\xfa\x00\x19\x00\x41\x00\x0b\x00\x0b\x00\x9f\x00\xa0\x00\xa1\x00\x1a\x00\x0c\x00\x06\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x0d\x00\x0d\x00\x0a\x01\x1b\x00\x0e\x00\x0e\x00\x68\x00\xfb\x00\x22\x00\xe7\x00\xfc\x00\x69\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x0f\x00\x1c\x00\x1d\x00\x55\x00\x1e\x00\x0b\x00\x56\x00\x57\x00\x0b\x00\xe8\x00\x0c\x00\x58\x00\x59\x00\x0c\x00\xea\x00\x5a\x00\xec\x00\x0d\x00\xf1\x00\x5b\x00\x0d\x00\x0e\x00\x5c\x00\xf2\x00\x0e\x00\x5d\x00\x5e\x00\xf3\x00\x5f\x00\x60\x00\x61\x00\xf4\x00\x0f\x00\xdb\x00\xdd\x00\x0f\x00\xdf\x00\x06\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x22\x00\x2a\x00\x19\x00\xba\x00\x0b\x00\x2b\x00\x2c\x00\xc2\x00\x56\x00\x1a\x00\x2d\x00\x2e\x00\x2f\x00\x58\x00\x59\x00\xbc\x00\x0d\x00\xc3\x00\x30\x00\x1b\x00\x0e\x00\x31\x00\x81\x00\xc4\x00\x5c\x00\x62\x00\x32\x00\x33\x00\x64\x00\x08\x00\x09\x00\x0f\x00\xff\xff\x1c\x00\x1d\x00\x22\x00\x1e\x00\x55\x00\xa5\x00\x0b\x00\x56\x00\x57\x00\xae\x00\xaf\x00\x0c\x00\x58\x00\x59\x00\x68\x00\x82\x00\x5a\x00\x85\x00\x0d\x00\x92\x00\x5b\x00\x98\x00\x0e\x00\x5c\x00\x8f\x00\xe2\x00\x5d\x00\x5e\x00\x99\x00\x5f\x00\x60\x00\x61\x00\x35\x00\x0f\x00\x38\x00\x63\x00\x06\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x2a\x00\xf9\x00\xd3\x00\xd4\x00\x2b\x00\x2c\x00\xd2\x00\xd3\x00\xd4\x00\x2d\x00\x2e\x00\x2f\x00\x10\x01\x37\x00\x44\x00\x1d\x01\x0b\x00\x30\x00\x11\x01\x38\x00\x31\x00\x0c\x00\x66\x00\x08\x00\x09\x00\x32\x00\x33\x00\x62\x00\x0d\x00\x1f\x01\x05\x01\x46\x00\x0e\x00\x06\x01\x22\x00\x13\x01\x47\x00\x48\x00\x08\x01\x07\x01\x49\x00\x09\x01\x0a\x01\x0f\x00\x4a\x00\x0f\x01\x4b\x00\x0b\x00\xd0\x00\xd1\x00\x4d\x00\x2a\x00\x0c\x00\xf9\x00\x02\x01\x2b\x00\x2c\x00\xee\x00\xef\x00\x0d\x00\x2d\x00\x2e\x00\x2f\x00\x0e\x00\x37\x00\xf0\x00\x22\x00\xd0\x00\x30\x00\xd1\x00\x38\x00\x31\x00\xdd\x00\xd2\x00\x0f\x00\xdf\x00\x32\x00\x33\x00\x0b\x00\xe3\x00\x1c\x01\xe4\x00\x2a\x00\x0c\x00\xbf\x00\x22\x00\x2b\x00\x2c\x00\x22\x00\x4e\x00\x0d\x00\x2d\x00\x2e\x00\x2f\x00\x0e\x00\x37\x00\xbe\x00\x22\x00\xc0\x00\x30\x00\xc2\x00\x38\x00\x31\x00\xc1\x00\x22\x00\x0f\x00\x06\x00\x32\x00\x33\x00\x0b\x00\xc6\x00\x17\x01\xc7\x00\x2a\x00\x0c\x00\x59\x00\x22\x00\x2b\x00\x2c\x00\xc8\x00\xc9\x00\x0d\x00\x2d\x00\x2e\x00\x2f\x00\x0e\x00\x37\x00\x22\x00\xb1\x00\xb4\x00\x30\x00\x6f\x00\x38\x00\x31\x00\x22\x00\x6f\x00\x0f\x00\x8f\x00\x32\x00\x33\x00\x0b\x00\xff\xff\x19\x01\x3a\x00\x2a\x00\x0c\x00\x3b\x00\x22\x00\x2b\x00\x2c\x00\x3c\x00\x3d\x00\x0d\x00\x2d\x00\x2e\x00\x2f\x00\x0e\x00\x37\x00\x42\x00\x44\x00\x63\x00\x30\x00\x43\x00\x38\x00\x31\x00\x6b\x00\x22\x00\x0f\x00\x4f\x00\x32\x00\x33\x00\x0b\x00\xff\xff\x12\x01\xff\xff\x2a\x00\x0c\x00\x06\x00\x22\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x0d\x00\x2d\x00\x2e\x00\x2f\x00\x0e\x00\x37\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x38\x00\x31\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x32\x00\x33\x00\x0b\x00\x00\x00\x00\x01\x00\x00\x2a\x00\x0c\x00\x00\x00\x22\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x0d\x00\x2d\x00\x2e\x00\x2f\x00\x0e\x00\x37\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x38\x00\x31\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x32\x00\x33\x00\x0b\x00\x00\x00\xea\x00\x00\x00\x2a\x00\x0c\x00\x00\x00\x22\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x0d\x00\x2d\x00\x2e\x00\x2f\x00\x0e\x00\x37\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x38\x00\x31\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x32\x00\x33\x00\x0b\x00\x00\x00\xec\x00\x00\x00\x2a\x00\x0c\x00\x00\x00\x22\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x0d\x00\x2d\x00\x2e\x00\x2f\x00\x0e\x00\x37\x00\x00\x00\x00\x00\x00\x00\x30\x00\x00\x00\x38\x00\x31\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x32\x00\x33\x00\x0b\x00\x00\x00\xa8\x00\x00\x00\x2a\x00\x0c\x00\x00\x00\x22\x00\x2b\x00\x2c\x00\x00\x00\x00\x00\x0d\x00\x2d\x00\x2e\x00\x2f\x00\x0e\x00\x37\x00\x00\x00\x00\x00\x00\x00\x30\x00\x87\x00\x38\x00\x31\x00\x00\x00\x88\x00\x0f\x00\x89\x00\x32\x00\x33\x00\x8a\x00\x00\x00\xb2\x00\x00\x00\x2a\x00\x00\x00\x8b\x00\x22\x00\x2b\x00\x2c\x00\x8c\x00\x00\x00\x00\x00\x2d\x00\x2e\x00\x2f\x00\x8d\x00\x37\x00\x00\x00\x00\x00\x00\x00\x30\x00\x8e\x00\x38\x00\x31\x00\x00\x00\x00\x00\x00\x00\x55\x00\x32\x00\x33\x00\x56\x00\x57\x00\x98\x00\x00\x00\x80\x00\x58\x00\x59\x00\x22\x00\x00\x00\x5a\x00\x00\x00\x00\x00\xb5\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x55\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x00\x00\x18\x01\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x00\x00\x00\x00\x55\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x62\x00\x03\x01\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x55\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x62\x00\x04\x01\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x00\x00\x00\x00\x55\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x62\x00\xa7\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x55\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x62\x00\xa9\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x00\x00\x00\x00\x55\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x62\x00\xaa\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x55\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x62\x00\x00\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\xb3\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x00\x00\x55\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x00\x00\x62\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\xb5\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x55\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x00\x00\x62\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\xac\x00\x07\x00\x08\x00\x09\x00\x00\x00\x00\x00\xb6\x00\x55\x00\x62\x00\x00\x00\x56\x00\x57\x00\x00\x00\x00\x00\x80\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x55\x00\x62\x00\x00\x00\x56\x00\x57\x00\x00\x00\x00\x00\x00\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x46\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x47\x00\x48\x00\x5d\x00\x5e\x00\x49\x00\x5f\x00\x60\x00\x61\x00\x4a\x00\x00\x00\x4b\x00\x4c\x00\x3d\x00\x00\x00\x4d\x00\x00\x00\x62\x00\x3e\x00\x07\x00\x08\x00\x09\x00\x3d\x00\x00\x00\x00\x00\x00\x00\x3d\x00\x3e\x00\x07\x00\x08\x00\x09\x00\x3e\x00\x07\x00\x08\x00\x09\x00\x00\x00\x13\x00\x00\x00\x00\x00\x22\x00\x00\x00\x23\x00\x07\x00\x08\x00\x09\x00\x62\x00\x00\x00\x94\x00\x00\x00\xe6\x00\x4f\x00\x07\x00\x08\x00\x09\x00\x4e\x00\x00\x00\x00\x00\x00\x00\xab\x00\x00\x00\x00\x00\x00\x00\x3f\x00\x95\x00\x96\x00\x00\x00\x25\x00\x26\x00\x27\x00\x13\x00\x28\x00\x00\x00\x22\x00\x00\x00\x23\x00\x07\x00\x08\x00\x09\x00\x9a\x00\x9b\x00\x9c\x00\x9d\x00\x9e\x00\xa7\xff\x9f\x00\xa0\x00\xa1\x00\xa7\xff\x00\x00\xa7\xff\x00\x00\x00\x00\xa7\xff\xd6\x00\x00\x00\x00\x00\x00\x00\x24\x00\xa7\xff\x25\x00\x26\x00\x27\x00\xa7\xff\x28\x00\xd7\x00\xd8\x00\xd9\x00\x55\x00\xa7\xff\x00\x00\x56\x00\x57\x00\xda\x00\xdb\x00\xa7\xff\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x56\x00\x5f\x00\x60\x00\x61\x00\x00\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x55\x00\x00\x00\x00\x00\x56\x00\x00\x00\x00\x00\x00\x00\x00\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x56\x00\x5f\x00\x60\x00\x61\x00\x00\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x55\x00\x00\x00\x00\x00\x56\x00\x00\x00\x00\x00\x00\x00\x00\x00\x58\x00\x59\x00\x00\x00\x00\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x5d\x00\x5e\x00\x00\x00\x5f\x00\x60\x00\x61\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x6f\x00\x16\x00\xf5\x00\x17\x00\x07\x00\x08\x00\x09\x00\x67\x00\x07\x00\x08\x00\x09\x00\x06\x00\x07\x00\x08\x00\x09\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1a\x01\x0d\x01\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x0b\x01\x16\x00\xf5\x00\x52\x00\x07\x00\x08\x00\x09\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0c\x01\x0d\x01\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x6f\x00\x16\x00\xf5\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x6f\x00\x16\x00\xb6\x00\x17\x00\x07\x00\x08\x00\x09\x00\xf6\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x6f\x00\x16\x00\x70\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x14\x01\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x00\x01\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\xe4\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\xe5\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\xf0\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\xe0\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\xb9\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\xaa\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x6d\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x71\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x72\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x73\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x74\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x75\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x76\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x77\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x78\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x79\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x7a\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x7b\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x7c\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x7d\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x7e\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x80\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x90\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x91\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x93\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x50\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x51\x00\x16\x00\x00\x00\x52\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x53\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x15\x00\x16\x00\x00\x00\x17\x00\x07\x00\x08\x00\x09\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (4, 133) [
	(4 , happyReduce_4),
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65),
	(66 , happyReduce_66),
	(67 , happyReduce_67),
	(68 , happyReduce_68),
	(69 , happyReduce_69),
	(70 , happyReduce_70),
	(71 , happyReduce_71),
	(72 , happyReduce_72),
	(73 , happyReduce_73),
	(74 , happyReduce_74),
	(75 , happyReduce_75),
	(76 , happyReduce_76),
	(77 , happyReduce_77),
	(78 , happyReduce_78),
	(79 , happyReduce_79),
	(80 , happyReduce_80),
	(81 , happyReduce_81),
	(82 , happyReduce_82),
	(83 , happyReduce_83),
	(84 , happyReduce_84),
	(85 , happyReduce_85),
	(86 , happyReduce_86),
	(87 , happyReduce_87),
	(88 , happyReduce_88),
	(89 , happyReduce_89),
	(90 , happyReduce_90),
	(91 , happyReduce_91),
	(92 , happyReduce_92),
	(93 , happyReduce_93),
	(94 , happyReduce_94),
	(95 , happyReduce_95),
	(96 , happyReduce_96),
	(97 , happyReduce_97),
	(98 , happyReduce_98),
	(99 , happyReduce_99),
	(100 , happyReduce_100),
	(101 , happyReduce_101),
	(102 , happyReduce_102),
	(103 , happyReduce_103),
	(104 , happyReduce_104),
	(105 , happyReduce_105),
	(106 , happyReduce_106),
	(107 , happyReduce_107),
	(108 , happyReduce_108),
	(109 , happyReduce_109),
	(110 , happyReduce_110),
	(111 , happyReduce_111),
	(112 , happyReduce_112),
	(113 , happyReduce_113),
	(114 , happyReduce_114),
	(115 , happyReduce_115),
	(116 , happyReduce_116),
	(117 , happyReduce_117),
	(118 , happyReduce_118),
	(119 , happyReduce_119),
	(120 , happyReduce_120),
	(121 , happyReduce_121),
	(122 , happyReduce_122),
	(123 , happyReduce_123),
	(124 , happyReduce_124),
	(125 , happyReduce_125),
	(126 , happyReduce_126),
	(127 , happyReduce_127),
	(128 , happyReduce_128),
	(129 , happyReduce_129),
	(130 , happyReduce_130),
	(131 , happyReduce_131),
	(132 , happyReduce_132),
	(133 , happyReduce_133)
	]

happy_n_terms = 74 :: Int
happy_n_nonterms = 41 :: Int

happyReduce_4 = happySpecReduce_1  0# happyReduction_4
happyReduction_4 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TI happy_var_1)) -> 
	happyIn7
		 ((read ( happy_var_1)) :: Integer
	)}

happyReduce_5 = happySpecReduce_1  1# happyReduction_5
happyReduction_5 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TC happy_var_1)) -> 
	happyIn8
		 ((read ( happy_var_1)) :: Char
	)}

happyReduce_6 = happySpecReduce_1  2# happyReduction_6
happyReduction_6 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TL happy_var_1)) -> 
	happyIn9
		 (happy_var_1
	)}

happyReduce_7 = happySpecReduce_1  3# happyReduction_7
happyReduction_7 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TD happy_var_1)) -> 
	happyIn10
		 ((read ( happy_var_1)) :: Double
	)}

happyReduce_8 = happySpecReduce_1  4# happyReduction_8
happyReduction_8 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TV happy_var_1)) -> 
	happyIn11
		 (Ident happy_var_1
	)}

happyReduce_9 = happySpecReduce_1  5# happyReduction_9
happyReduction_9 happy_x_1
	 =  happyIn12
		 (AbsPerl.Boolean_True
	)

happyReduce_10 = happySpecReduce_1  5# happyReduction_10
happyReduction_10 happy_x_1
	 =  happyIn12
		 (AbsPerl.Boolean_False
	)

happyReduce_11 = happySpecReduce_3  6# happyReduction_11
happyReduction_11 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_2 of { happy_var_2 -> 
	happyIn13
		 (happy_var_2
	)}

happyReduce_12 = happySpecReduce_3  6# happyReduction_12
happyReduction_12 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (BoolOp Or)   happy_var_1 happy_var_3
	)}}

happyReduce_13 = happySpecReduce_3  6# happyReduction_13
happyReduction_13 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (BoolOp And)  happy_var_1 happy_var_3
	)}}

happyReduce_14 = happySpecReduce_3  6# happyReduction_14
happyReduction_14 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp Eq)    happy_var_1 happy_var_3
	)}}

happyReduce_15 = happySpecReduce_3  6# happyReduction_15
happyReduction_15 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp Neq)   happy_var_1 happy_var_3
	)}}

happyReduce_16 = happySpecReduce_3  6# happyReduction_16
happyReduction_16 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp Lt)    happy_var_1 happy_var_3
	)}}

happyReduce_17 = happySpecReduce_3  6# happyReduction_17
happyReduction_17 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp LtE)   happy_var_1 happy_var_3
	)}}

happyReduce_18 = happySpecReduce_3  6# happyReduction_18
happyReduction_18 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp Gt)    happy_var_1 happy_var_3
	)}}

happyReduce_19 = happySpecReduce_3  6# happyReduction_19
happyReduction_19 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (RelOp GtE)   happy_var_1 happy_var_3
	)}}

happyReduce_20 = happySpecReduce_3  6# happyReduction_20
happyReduction_20 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Add) happy_var_1 happy_var_3
	)}}

happyReduce_21 = happySpecReduce_3  6# happyReduction_21
happyReduction_21 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Sub) happy_var_1 happy_var_3
	)}}

happyReduce_22 = happySpecReduce_3  6# happyReduction_22
happyReduction_22 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Mul) happy_var_1 happy_var_3
	)}}

happyReduce_23 = happySpecReduce_3  6# happyReduction_23
happyReduction_23 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Div) happy_var_1 happy_var_3
	)}}

happyReduce_24 = happySpecReduce_3  6# happyReduction_24
happyReduction_24 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Mod) happy_var_1 happy_var_3
	)}}

happyReduce_25 = happySpecReduce_3  6# happyReduction_25
happyReduction_25 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (InfixOp (ArithOp Pow) happy_var_1 happy_var_3
	)}}

happyReduce_26 = happySpecReduce_2  6# happyReduction_26
happyReduction_26 happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_2 of { happy_var_2 -> 
	happyIn13
		 (UnaryOp Not happy_var_2
	)}

happyReduce_27 = happySpecReduce_2  6# happyReduction_27
happyReduction_27 happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_2 of { happy_var_2 -> 
	happyIn13
		 (UnaryOp Neg happy_var_2
	)}

happyReduce_28 = happySpecReduce_2  6# happyReduction_28
happyReduction_28 happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_2 of { happy_var_2 -> 
	happyIn13
		 (Ref happy_var_2
	)}

happyReduce_29 = happySpecReduce_1  6# happyReduction_29
happyReduction_29 happy_x_1
	 =  case happyOut16 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (Lexpr happy_var_1
	)}

happyReduce_30 = happySpecReduce_1  6# happyReduction_30
happyReduction_30 happy_x_1
	 =  case happyOut14 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (FCall happy_var_1
	)}

happyReduce_31 = happySpecReduce_1  6# happyReduction_31
happyReduction_31 happy_x_1
	 =  case happyOut7 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (AbsPerl.Int happy_var_1
	)}

happyReduce_32 = happySpecReduce_1  6# happyReduction_32
happyReduction_32 happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (AbsPerl.Char happy_var_1
	)}

happyReduce_33 = happySpecReduce_1  6# happyReduction_33
happyReduction_33 happy_x_1
	 =  case happyOut9 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (AbsPerl.String happy_var_1
	)}

happyReduce_34 = happySpecReduce_1  6# happyReduction_34
happyReduction_34 happy_x_1
	 =  case happyOut10 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (AbsPerl.Float happy_var_1
	)}

happyReduce_35 = happySpecReduce_1  6# happyReduction_35
happyReduction_35 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (AbsPerl.Bool happy_var_1
	)}

happyReduce_36 = happyReduce 4# 7# happyReduction_36
happyReduction_36 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut11 happy_x_1 of { happy_var_1 -> 
	case happyOut15 happy_x_3 of { happy_var_3 -> 
	happyIn14
		 (AbsPerl.Call happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_37 = happySpecReduce_0  8# happyReduction_37
happyReduction_37  =  happyIn15
		 ([]
	)

happyReduce_38 = happySpecReduce_1  8# happyReduction_38
happyReduction_38 happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	happyIn15
		 ((:[]) happy_var_1
	)}

happyReduce_39 = happySpecReduce_3  8# happyReduction_39
happyReduction_39 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut15 happy_x_3 of { happy_var_3 -> 
	happyIn15
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_40 = happySpecReduce_1  9# happyReduction_40
happyReduction_40 happy_x_1
	 =  case happyOut17 happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (happy_var_1
	)}

happyReduce_41 = happySpecReduce_2  9# happyReduction_41
happyReduction_41 happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_2 of { happy_var_2 -> 
	happyIn16
		 (AbsPerl.Deref happy_var_2
	)}

happyReduce_42 = happySpecReduce_2  9# happyReduction_42
happyReduction_42 happy_x_2
	happy_x_1
	 =  case happyOut17 happy_x_2 of { happy_var_2 -> 
	happyIn16
		 (PrePostIncDecr Pre Inc happy_var_2
	)}

happyReduce_43 = happySpecReduce_2  9# happyReduction_43
happyReduction_43 happy_x_2
	happy_x_1
	 =  case happyOut17 happy_x_2 of { happy_var_2 -> 
	happyIn16
		 (PrePostIncDecr Pre Decr happy_var_2
	)}

happyReduce_44 = happySpecReduce_1  10# happyReduction_44
happyReduction_44 happy_x_1
	 =  case happyOut18 happy_x_1 of { happy_var_1 -> 
	happyIn17
		 (happy_var_1
	)}

happyReduce_45 = happySpecReduce_2  10# happyReduction_45
happyReduction_45 happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { happy_var_1 -> 
	happyIn17
		 (PrePostIncDecr Post Inc happy_var_1
	)}

happyReduce_46 = happySpecReduce_2  10# happyReduction_46
happyReduction_46 happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { happy_var_1 -> 
	happyIn17
		 (PrePostIncDecr Post Decr happy_var_1
	)}

happyReduce_47 = happySpecReduce_3  11# happyReduction_47
happyReduction_47 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_2 of { happy_var_2 -> 
	happyIn18
		 (happy_var_2
	)}

happyReduce_48 = happySpecReduce_1  11# happyReduction_48
happyReduction_48 happy_x_1
	 =  case happyOut19 happy_x_1 of { happy_var_1 -> 
	happyIn18
		 (AbsPerl.BasLExpr happy_var_1
	)}

happyReduce_49 = happyReduce 4# 12# happyReduction_49
happyReduction_49 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn19
		 (AbsPerl.ArrayEl happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_50 = happySpecReduce_2  12# happyReduction_50
happyReduction_50 happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_2 of { happy_var_2 -> 
	happyIn19
		 (AbsPerl.Id happy_var_2
	)}

happyReduce_51 = happySpecReduce_2  12# happyReduction_51
happyReduction_51 happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_2 of { happy_var_2 -> 
	happyIn19
		 (AbsPerl.Id happy_var_2
	)}

happyReduce_52 = happySpecReduce_1  13# happyReduction_52
happyReduction_52 happy_x_1
	 =  case happyOut21 happy_x_1 of { happy_var_1 -> 
	happyIn20
		 (AbsPerl.Prog (reverse happy_var_1)
	)}

happyReduce_53 = happySpecReduce_0  14# happyReduction_53
happyReduction_53  =  happyIn21
		 ([]
	)

happyReduce_54 = happySpecReduce_2  14# happyReduction_54
happyReduction_54 happy_x_2
	happy_x_1
	 =  case happyOut21 happy_x_1 of { happy_var_1 -> 
	case happyOut22 happy_x_2 of { happy_var_2 -> 
	happyIn21
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_55 = happyReduce 4# 15# happyReduction_55
happyReduction_55 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_2 of { happy_var_2 -> 
	case happyOut23 happy_x_3 of { happy_var_3 -> 
	happyIn22
		 (AbsPerl.Dvar happy_var_2 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_56 = happyReduce 4# 15# happyReduction_56
happyReduction_56 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_2 of { happy_var_2 -> 
	case happyOut24 happy_x_3 of { happy_var_3 -> 
	happyIn22
		 (AbsPerl.UndVar happy_var_2 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_57 = happyReduce 9# 15# happyReduction_57
happyReduction_57 (happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_2 of { happy_var_2 -> 
	case happyOut11 happy_x_3 of { happy_var_3 -> 
	case happyOut34 happy_x_5 of { happy_var_5 -> 
	case happyOut37 happy_x_8 of { happy_var_8 -> 
	happyIn22
		 (AbsPerl.Dfun happy_var_2 happy_var_3 happy_var_5 (reverse happy_var_8)
	) `HappyStk` happyRest}}}}

happyReduce_58 = happySpecReduce_1  16# happyReduction_58
happyReduction_58 happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	happyIn23
		 ((:[]) happy_var_1
	)}

happyReduce_59 = happySpecReduce_3  16# happyReduction_59
happyReduction_59 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	case happyOut23 happy_x_3 of { happy_var_3 -> 
	happyIn23
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_60 = happySpecReduce_1  17# happyReduction_60
happyReduction_60 happy_x_1
	 =  case happyOut25 happy_x_1 of { happy_var_1 -> 
	happyIn24
		 ((:[]) happy_var_1
	)}

happyReduce_61 = happySpecReduce_3  17# happyReduction_61
happyReduction_61 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut25 happy_x_1 of { happy_var_1 -> 
	case happyOut24 happy_x_3 of { happy_var_3 -> 
	happyIn24
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_62 = happySpecReduce_1  18# happyReduction_62
happyReduction_62 happy_x_1
	 =  case happyOut26 happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (AbsPerl.UndVarD happy_var_1
	)}

happyReduce_63 = happySpecReduce_1  18# happyReduction_63
happyReduction_63 happy_x_1
	 =  case happyOut27 happy_x_1 of { happy_var_1 -> 
	happyIn25
		 (AbsPerl.UndVarA happy_var_1
	)}

happyReduce_64 = happySpecReduce_2  19# happyReduction_64
happyReduction_64 happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_2 of { happy_var_2 -> 
	happyIn26
		 (AbsPerl.UndA happy_var_2
	)}

happyReduce_65 = happySpecReduce_2  20# happyReduction_65
happyReduction_65 happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_2 of { happy_var_2 -> 
	happyIn27
		 (AbsPerl.UndV happy_var_2
	)}

happyReduce_66 = happyReduce 4# 21# happyReduction_66
happyReduction_66 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut7 happy_x_3 of { happy_var_3 -> 
	happyIn28
		 (AbsPerl.ArrDef happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_67 = happySpecReduce_2  21# happyReduction_67
happyReduction_67 happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_2 of { happy_var_2 -> 
	happyIn28
		 (AbsPerl.Pointer happy_var_2
	)}

happyReduce_68 = happySpecReduce_1  21# happyReduction_68
happyReduction_68 happy_x_1
	 =  happyIn28
		 (T_Bool
	)

happyReduce_69 = happySpecReduce_1  21# happyReduction_69
happyReduction_69 happy_x_1
	 =  happyIn28
		 (T_Char
	)

happyReduce_70 = happySpecReduce_1  21# happyReduction_70
happyReduction_70 happy_x_1
	 =  happyIn28
		 (T_Float
	)

happyReduce_71 = happySpecReduce_1  21# happyReduction_71
happyReduction_71 happy_x_1
	 =  happyIn28
		 (T_Int
	)

happyReduce_72 = happySpecReduce_1  21# happyReduction_72
happyReduction_72 happy_x_1
	 =  happyIn28
		 (T_Void
	)

happyReduce_73 = happySpecReduce_1  21# happyReduction_73
happyReduction_73 happy_x_1
	 =  happyIn28
		 (T_String
	)

happyReduce_74 = happySpecReduce_1  21# happyReduction_74
happyReduction_74 happy_x_1
	 =  happyIn28
		 (T_Error
	)

happyReduce_75 = happySpecReduce_1  22# happyReduction_75
happyReduction_75 happy_x_1
	 =  case happyOut30 happy_x_1 of { happy_var_1 -> 
	happyIn29
		 (AbsPerl.VarDeclInA happy_var_1
	)}

happyReduce_76 = happySpecReduce_1  22# happyReduction_76
happyReduction_76 happy_x_1
	 =  case happyOut31 happy_x_1 of { happy_var_1 -> 
	happyIn29
		 (AbsPerl.VarDeclInV happy_var_1
	)}

happyReduce_77 = happyReduce 6# 23# happyReduction_77
happyReduction_77 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut11 happy_x_2 of { happy_var_2 -> 
	case happyOut33 happy_x_5 of { happy_var_5 -> 
	happyIn30
		 (AbsPerl.VarDeclInitAr happy_var_2 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_78 = happyReduce 4# 24# happyReduction_78
happyReduction_78 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut11 happy_x_2 of { happy_var_2 -> 
	case happyOut13 happy_x_4 of { happy_var_4 -> 
	happyIn31
		 (AbsPerl.VarDeclInitV happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_79 = happySpecReduce_0  25# happyReduction_79
happyReduction_79  =  happyIn32
		 ([]
	)

happyReduce_80 = happySpecReduce_1  25# happyReduction_80
happyReduction_80 happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 ((:[]) happy_var_1
	)}

happyReduce_81 = happySpecReduce_3  25# happyReduction_81
happyReduction_81 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	case happyOut32 happy_x_3 of { happy_var_3 -> 
	happyIn32
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_82 = happySpecReduce_3  26# happyReduction_82
happyReduction_82 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut32 happy_x_2 of { happy_var_2 -> 
	happyIn33
		 (AbsPerl.Arr happy_var_2
	)}

happyReduce_83 = happySpecReduce_1  26# happyReduction_83
happyReduction_83 happy_x_1
	 =  case happyOut15 happy_x_1 of { happy_var_1 -> 
	happyIn33
		 (AbsPerl.ArrE  happy_var_1
	)}

happyReduce_84 = happySpecReduce_0  27# happyReduction_84
happyReduction_84  =  happyIn34
		 ([]
	)

happyReduce_85 = happySpecReduce_1  27# happyReduction_85
happyReduction_85 happy_x_1
	 =  case happyOut35 happy_x_1 of { happy_var_1 -> 
	happyIn34
		 ((:[]) happy_var_1
	)}

happyReduce_86 = happySpecReduce_3  27# happyReduction_86
happyReduction_86 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut35 happy_x_1 of { happy_var_1 -> 
	case happyOut34 happy_x_3 of { happy_var_3 -> 
	happyIn34
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_87 = happySpecReduce_3  28# happyReduction_87
happyReduction_87 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut36 happy_x_1 of { happy_var_1 -> 
	case happyOut28 happy_x_2 of { happy_var_2 -> 
	case happyOut11 happy_x_3 of { happy_var_3 -> 
	happyIn35
		 (AbsPerl.Param happy_var_1 happy_var_2 happy_var_3
	)}}}

happyReduce_88 = happySpecReduce_0  29# happyReduction_88
happyReduction_88  =  happyIn36
		 (M_Void
	)

happyReduce_89 = happySpecReduce_1  29# happyReduction_89
happyReduction_89 happy_x_1
	 =  happyIn36
		 (M_Val
	)

happyReduce_90 = happySpecReduce_1  29# happyReduction_90
happyReduction_90 happy_x_1
	 =  happyIn36
		 (M_Ref
	)

happyReduce_91 = happySpecReduce_1  29# happyReduction_91
happyReduction_91 happy_x_1
	 =  happyIn36
		 (M_Const
	)

happyReduce_92 = happySpecReduce_1  29# happyReduction_92
happyReduction_92 happy_x_1
	 =  happyIn36
		 (M_Res
	)

happyReduce_93 = happySpecReduce_1  29# happyReduction_93
happyReduction_93 happy_x_1
	 =  happyIn36
		 (M_Valres
	)

happyReduce_94 = happySpecReduce_1  29# happyReduction_94
happyReduction_94 happy_x_1
	 =  happyIn36
		 (M_Name
	)

happyReduce_95 = happySpecReduce_0  30# happyReduction_95
happyReduction_95  =  happyIn37
		 ([]
	)

happyReduce_96 = happySpecReduce_2  30# happyReduction_96
happyReduction_96 happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOut38 happy_x_2 of { happy_var_2 -> 
	happyIn37
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_97 = happySpecReduce_1  31# happyReduction_97
happyReduction_97 happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	happyIn38
		 (AbsPerl.Decls happy_var_1
	)}

happyReduce_98 = happySpecReduce_1  31# happyReduction_98
happyReduction_98 happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	happyIn38
		 (AbsPerl.Stmts happy_var_1
	)}

happyReduce_99 = happySpecReduce_2  32# happyReduction_99
happyReduction_99 happy_x_2
	happy_x_1
	 =  case happyOut14 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (AbsPerl.ProcCall happy_var_1
	)}

happyReduce_100 = happySpecReduce_3  32# happyReduction_100
happyReduction_100 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_2 of { happy_var_2 -> 
	happyIn39
		 (AbsPerl.BlockDecl (reverse happy_var_2)
	)}

happyReduce_101 = happySpecReduce_2  32# happyReduction_101
happyReduction_101 happy_x_2
	happy_x_1
	 =  case happyOut42 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (AbsPerl.Jmp happy_var_1
	)}

happyReduce_102 = happySpecReduce_1  32# happyReduction_102
happyReduction_102 happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (AbsPerl.Iter happy_var_1
	)}

happyReduce_103 = happySpecReduce_1  32# happyReduction_103
happyReduction_103 happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (AbsPerl.Sel happy_var_1
	)}

happyReduce_104 = happySpecReduce_1  32# happyReduction_104
happyReduction_104 happy_x_1
	 =  case happyOut41 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (AbsPerl.TryC happy_var_1
	)}

happyReduce_105 = happyReduce 4# 32# happyReduction_105
happyReduction_105 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut16 happy_x_1 of { happy_var_1 -> 
	case happyOut40 happy_x_2 of { happy_var_2 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn39
		 (AbsPerl.Assgn happy_var_1 happy_var_2 happy_var_3
	) `HappyStk` happyRest}}}

happyReduce_106 = happySpecReduce_2  32# happyReduction_106
happyReduction_106 happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (AbsPerl.LExprStmt happy_var_1
	)}

happyReduce_107 = happySpecReduce_1  33# happyReduction_107
happyReduction_107 happy_x_1
	 =  happyIn40
		 (AbsPerl.Assign
	)

happyReduce_108 = happySpecReduce_1  33# happyReduction_108
happyReduction_108 happy_x_1
	 =  happyIn40
		 (AbsPerl.AssgnMul
	)

happyReduce_109 = happySpecReduce_1  33# happyReduction_109
happyReduction_109 happy_x_1
	 =  happyIn40
		 (AbsPerl.AssgnAdd
	)

happyReduce_110 = happySpecReduce_1  33# happyReduction_110
happyReduction_110 happy_x_1
	 =  happyIn40
		 (AbsPerl.AssgnDiv
	)

happyReduce_111 = happySpecReduce_1  33# happyReduction_111
happyReduction_111 happy_x_1
	 =  happyIn40
		 (AbsPerl.AssgnSub
	)

happyReduce_112 = happySpecReduce_1  33# happyReduction_112
happyReduction_112 happy_x_1
	 =  happyIn40
		 (AbsPerl.AssgnPow
	)

happyReduce_113 = happySpecReduce_1  33# happyReduction_113
happyReduction_113 happy_x_1
	 =  happyIn40
		 (AbsPerl.AssgnAnd
	)

happyReduce_114 = happySpecReduce_1  33# happyReduction_114
happyReduction_114 happy_x_1
	 =  happyIn40
		 (AbsPerl.AssgnOr
	)

happyReduce_115 = happyReduce 12# 34# happyReduction_115
happyReduction_115 (happy_x_12 `HappyStk`
	happy_x_11 `HappyStk`
	happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut37 happy_x_3 of { happy_var_3 -> 
	case happyOut28 happy_x_7 of { happy_var_7 -> 
	case happyOut9 happy_x_8 of { happy_var_8 -> 
	case happyOut37 happy_x_11 of { happy_var_11 -> 
	happyIn41
		 (AbsPerl.Try (reverse happy_var_3) happy_var_7 happy_var_8 (reverse happy_var_11)
	) `HappyStk` happyRest}}}}

happyReduce_116 = happySpecReduce_1  35# happyReduction_116
happyReduction_116 happy_x_1
	 =  happyIn42
		 (AbsPerl.Break
	)

happyReduce_117 = happySpecReduce_1  35# happyReduction_117
happyReduction_117 happy_x_1
	 =  happyIn42
		 (AbsPerl.Continue
	)

happyReduce_118 = happySpecReduce_1  35# happyReduction_118
happyReduction_118 happy_x_1
	 =  happyIn42
		 (AbsPerl.RetExpVoid
	)

happyReduce_119 = happyReduce 4# 35# happyReduction_119
happyReduction_119 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn42
		 (AbsPerl.RetExp happy_var_3
	) `HappyStk` happyRest}

happyReduce_120 = happyReduce 7# 36# happyReduction_120
happyReduction_120 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_3 of { happy_var_3 -> 
	case happyOut37 happy_x_6 of { happy_var_6 -> 
	happyIn43
		 (AbsPerl.IfNoElse happy_var_3 (reverse happy_var_6)
	) `HappyStk` happyRest}}

happyReduce_121 = happyReduce 8# 36# happyReduction_121
happyReduction_121 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_3 of { happy_var_3 -> 
	case happyOut37 happy_x_6 of { happy_var_6 -> 
	case happyOut44 happy_x_8 of { happy_var_8 -> 
	happyIn43
		 (AbsPerl.ElseIf happy_var_3 (reverse happy_var_6) happy_var_8
	) `HappyStk` happyRest}}}

happyReduce_122 = happyReduce 8# 37# happyReduction_122
happyReduction_122 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_3 of { happy_var_3 -> 
	case happyOut37 happy_x_6 of { happy_var_6 -> 
	case happyOut44 happy_x_8 of { happy_var_8 -> 
	happyIn44
		 (AbsPerl.IfElsIf happy_var_3 (reverse happy_var_6) happy_var_8
	) `HappyStk` happyRest}}}

happyReduce_123 = happyReduce 4# 37# happyReduction_123
happyReduction_123 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut37 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (AbsPerl.EndElsIf (reverse happy_var_3)
	) `HappyStk` happyRest}

happyReduce_124 = happyReduce 7# 38# happyReduction_124
happyReduction_124 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_3 of { happy_var_3 -> 
	case happyOut37 happy_x_6 of { happy_var_6 -> 
	happyIn45
		 (AbsPerl.While happy_var_3 (reverse happy_var_6)
	) `HappyStk` happyRest}}

happyReduce_125 = happyReduce 9# 38# happyReduction_125
happyReduction_125 (happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut37 happy_x_3 of { happy_var_3 -> 
	case happyOut13 happy_x_7 of { happy_var_7 -> 
	happyIn45
		 (AbsPerl.DoWhile (reverse happy_var_3) happy_var_7
	) `HappyStk` happyRest}}

happyReduce_126 = happyReduce 9# 38# happyReduction_126
happyReduction_126 (happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut37 happy_x_3 of { happy_var_3 -> 
	case happyOut13 happy_x_7 of { happy_var_7 -> 
	happyIn45
		 (AbsPerl.DoUntil (reverse happy_var_3) happy_var_7
	) `HappyStk` happyRest}}

happyReduce_127 = happyReduce 11# 38# happyReduction_127
happyReduction_127 (happy_x_11 `HappyStk`
	happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut46 happy_x_3 of { happy_var_3 -> 
	case happyOut13 happy_x_5 of { happy_var_5 -> 
	case happyOut47 happy_x_7 of { happy_var_7 -> 
	case happyOut37 happy_x_10 of { happy_var_10 -> 
	happyIn45
		 (AbsPerl.For happy_var_3 happy_var_5 happy_var_7 (reverse happy_var_10)
	) `HappyStk` happyRest}}}}

happyReduce_128 = happyReduce 8# 38# happyReduction_128
happyReduction_128 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut47 happy_x_2 of { happy_var_2 -> 
	case happyOut47 happy_x_4 of { happy_var_4 -> 
	case happyOut37 happy_x_7 of { happy_var_7 -> 
	happyIn45
		 (AbsPerl.ForEach happy_var_2 happy_var_4 (reverse happy_var_7)
	) `HappyStk` happyRest}}}

happyReduce_129 = happyReduce 6# 39# happyReduction_129
happyReduction_129 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_2 of { happy_var_2 -> 
	case happyOut11 happy_x_4 of { happy_var_4 -> 
	case happyOut40 happy_x_5 of { happy_var_5 -> 
	case happyOut13 happy_x_6 of { happy_var_6 -> 
	happyIn46
		 (AbsPerl.ForDeclInit happy_var_2 happy_var_4 happy_var_5 happy_var_6
	) `HappyStk` happyRest}}}}

happyReduce_130 = happyReduce 4# 39# happyReduction_130
happyReduction_130 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut11 happy_x_2 of { happy_var_2 -> 
	case happyOut40 happy_x_3 of { happy_var_3 -> 
	case happyOut13 happy_x_4 of { happy_var_4 -> 
	happyIn46
		 (AbsPerl.Simple happy_var_2 happy_var_3 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_131 = happySpecReduce_1  40# happyReduction_131
happyReduction_131 happy_x_1
	 =  case happyOut16 happy_x_1 of { happy_var_1 -> 
	happyIn47
		 (AbsPerl.LexprForStmt happy_var_1
	)}

happyReduce_132 = happyReduce 4# 40# happyReduction_132
happyReduction_132 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_2 of { happy_var_2 -> 
	case happyOut11 happy_x_4 of { happy_var_4 -> 
	happyIn47
		 (AbsPerl.ForDecl happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_133 = happySpecReduce_3  40# happyReduction_133
happyReduction_133 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_1 of { happy_var_1 -> 
	case happyOut40 happy_x_2 of { happy_var_2 -> 
	case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn47
		 (AbsPerl.AssFor happy_var_1 happy_var_2 happy_var_3
	)}}}

happyNewToken action sts stk [] =
	happyDoAction 73# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (TS _ 10) -> cont 10#;
	PT _ (TS _ 11) -> cont 11#;
	PT _ (TS _ 12) -> cont 12#;
	PT _ (TS _ 13) -> cont 13#;
	PT _ (TS _ 14) -> cont 14#;
	PT _ (TS _ 15) -> cont 15#;
	PT _ (TS _ 16) -> cont 16#;
	PT _ (TS _ 17) -> cont 17#;
	PT _ (TS _ 18) -> cont 18#;
	PT _ (TS _ 19) -> cont 19#;
	PT _ (TS _ 20) -> cont 20#;
	PT _ (TS _ 21) -> cont 21#;
	PT _ (TS _ 22) -> cont 22#;
	PT _ (TS _ 23) -> cont 23#;
	PT _ (TS _ 24) -> cont 24#;
	PT _ (TS _ 25) -> cont 25#;
	PT _ (TS _ 26) -> cont 26#;
	PT _ (TS _ 27) -> cont 27#;
	PT _ (TS _ 28) -> cont 28#;
	PT _ (TS _ 29) -> cont 29#;
	PT _ (TS _ 30) -> cont 30#;
	PT _ (TS _ 31) -> cont 31#;
	PT _ (TS _ 32) -> cont 32#;
	PT _ (TS _ 33) -> cont 33#;
	PT _ (TS _ 34) -> cont 34#;
	PT _ (TS _ 35) -> cont 35#;
	PT _ (TS _ 36) -> cont 36#;
	PT _ (TS _ 37) -> cont 37#;
	PT _ (TS _ 38) -> cont 38#;
	PT _ (TS _ 39) -> cont 39#;
	PT _ (TS _ 40) -> cont 40#;
	PT _ (TS _ 41) -> cont 41#;
	PT _ (TS _ 42) -> cont 42#;
	PT _ (TS _ 43) -> cont 43#;
	PT _ (TS _ 44) -> cont 44#;
	PT _ (TS _ 45) -> cont 45#;
	PT _ (TS _ 46) -> cont 46#;
	PT _ (TS _ 47) -> cont 47#;
	PT _ (TS _ 48) -> cont 48#;
	PT _ (TS _ 49) -> cont 49#;
	PT _ (TS _ 50) -> cont 50#;
	PT _ (TS _ 51) -> cont 51#;
	PT _ (TS _ 52) -> cont 52#;
	PT _ (TS _ 53) -> cont 53#;
	PT _ (TS _ 54) -> cont 54#;
	PT _ (TS _ 55) -> cont 55#;
	PT _ (TS _ 56) -> cont 56#;
	PT _ (TS _ 57) -> cont 57#;
	PT _ (TS _ 58) -> cont 58#;
	PT _ (TS _ 59) -> cont 59#;
	PT _ (TS _ 60) -> cont 60#;
	PT _ (TS _ 61) -> cont 61#;
	PT _ (TS _ 62) -> cont 62#;
	PT _ (TS _ 63) -> cont 63#;
	PT _ (TS _ 64) -> cont 64#;
	PT _ (TS _ 65) -> cont 65#;
	PT _ (TS _ 66) -> cont 66#;
	PT _ (TS _ 67) -> cont 67#;
	PT _ (TI happy_dollar_dollar) -> cont 68#;
	PT _ (TC happy_dollar_dollar) -> cont 69#;
	PT _ (TL happy_dollar_dollar) -> cont 70#;
	PT _ (TD happy_dollar_dollar) -> cont 71#;
	PT _ (TV happy_dollar_dollar) -> cont 72#;
	_ -> happyError' (tk:tks)
	}

happyError_ 73# tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = (thenM)
happyReturn :: () => a -> Err a
happyReturn = (returnM)
happyThen1 m k tks = (thenM) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (returnM) a
happyError' :: () => [(Token)] -> Err a
happyError' = happyError

pProgram tks = happySomeParser where
  happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (happyOut20 x))

pStmt tks = happySomeParser where
  happySomeParser = happyThen (happyParse 1# tks) (\x -> happyReturn (happyOut39 x))

pRExpr tks = happySomeParser where
  happySomeParser = happyThen (happyParse 2# tks) (\x -> happyReturn (happyOut13 x))

pLExpr tks = happySomeParser where
  happySomeParser = happyThen (happyParse 3# tks) (\x -> happyReturn (happyOut16 x))

happySeq = happyDontSeq


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
{-# LINE 1 "templates/GenericTemplate.hs" #-}


















-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 







-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif



data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList


















infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is 0#, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}
          

          case action of
                0#           -> {- nothing -}
                                     happyFail i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}
                                                   
                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}
                                     

                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = indexShortOffAddr happyActOffsets st
         off_i  = (off Happy_GHC_Exts.+# i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else False
         action
          | check     = indexShortOffAddr happyTable off_i
          | otherwise = indexShortOffAddr happyDefActions st


indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#





data HappyAddr = HappyA# Happy_GHC_Exts.Addr#




-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = indexShortOffAddr happyGotoOffsets st1
             off_i = (off Happy_GHC_Exts.+# nt)
             new_state = indexShortOffAddr happyTable off_i



          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = indexShortOffAddr happyGotoOffsets st
         off_i = (off Happy_GHC_Exts.+# nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (0# is the error token)

-- parse error if we are in recovery and we fail again
happyFail 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  0# tk old_st (HappyCons ((action)) (sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        happyDoAction 0# tk action sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ( (Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.

