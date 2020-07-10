{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- bnfc produces an overlapping pattern and I haven't debugged it yet
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Refined where

import Language.LBNF

bnfc [lbnf|

  Nat. Term5 ::= Integer ;
  Succ. Term5 ::= "succ" ;
  Var. Term5 ::= Ident ;
  App. Term4 ::= Term4 Term5 ;
  PTrue. Term5 ::= "⊤" ;
  PFalse. Term5 ::= "⊥" ;
  PEquals. Term2 ::= Term3 "=" Term3 ;
  PNot. Term1 ::= "¬" Term1 ;
  PAnd. Term ::= Term1 "∧" Term ;
  PImpl. Term ::= Term1 "⇒" Term ;
  PEquiv. Term ::= Term1 "⇔" Term1 ;
  PForall. Term ::= "∀" Ident ":" RType "." Term ;

  coercions Term 5 ;
  separator Term1 "," ;

  INat. IType1 ::= "ℕ" ;
  IProp. IType1 ::= "Prop" ;
  IArrow. IType ::= IType1 "→" IType ;

  coercions IType 2 ;

  RNat. RType1 ::= "ℕ" ;
  RProp. RType1 ::= "Prop" ;
  RSub. RType1 ::= "{" Ident ":" RType "|" Term "}" ;
  RArrow. RType ::= RType1 "→" RType ;

  coercions RType 2 ;

  TId. TacExpr1 ::= "id" ;
  TDone. TacExpr1 ::= "done" ;
  TInd. TacExpr1 ::= "by" "induction" "on" Ident ;
  TIntros. TacExpr1 ::= "intros" ;
  THave. TacExpr1 ::= "have" Term "using" [Ident] ;
  TFocus. TacExpr1 ::= "focus" Term "using" [Ident] ;
  TWith. TacExpr1 ::= "with" Term ;
  TChain. TacExpr1 ::= "chain" ;
  TSplit. TacExpr1 ::= "split" ;
  TLeft. TacExpr1 ::= "left" ;
  TRight. TacExpr1 ::= "right" ;
  TPremise. TacExpr1 ::= "premise" ;
  TDeactivate. TacExpr1 ::= "deactivate" ;
  TUse. TacExpr1 ::= "use" Ident "with" [Term1] ;
  TSUse. TacExpr1 ::= "use" Ident ;
  TThen. TacExpr ::= TacExpr ";" TacExpr1 ;
  TDispatch. TacExpr ::= TacExpr ";" TacAlt ;

  coercions TacExpr 2 ;

  separator Ident "," ;
  separator TacExpr "|" ;

  TacAlt. TacAlt ::= "[" [TacExpr] "]" ;

  JustTacAlt. MaybeTacAlt ::= TacAlt ;
  NothingTacAlt. MaybeTacAlt ::= ;

  Definition. Decl ::= "def" Ident ":" RType ;
  Axiom. Decl ::= "ax" Ident ":" Term ;
  Theorem. Decl ::= "thm" Ident ":" Term MaybeTacAlt;

  []. [Decl] ::= ;
  (:). [Decl] ::= Decl [Decl] ;

  Prog. Prog ::= [Decl] ;

  entrypoints Prog, RType, IType, Term, TacExpr, MaybeTacAlt
|]
