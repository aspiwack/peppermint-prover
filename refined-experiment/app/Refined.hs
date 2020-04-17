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

  Nat. Term1 ::= Integer ;
  Succ. Term1 ::= "succ" ;
  Var. Term1 ::= Ident ;
  App. Term ::= Term Term1 ;

  coercions Term 3 ;
  separator Term1 "," ;

  INat. IType1 ::= "ℕ" ;
  IArrow. IType ::= IType1 "→" IType ;

  coercions IType 2 ;

  RNat. RType1 ::= "ℕ" ;
  RSub. RType1 ::= "{" Ident ":" RType "|" Prop "}" ;
  RArrow. RType ::= RType1 "→" RType ;

  coercions RType 2 ;

  PTrue. Prop2 ::= "⊤" ;
  PFalse. Prop2 ::= "⊥" ;
  PEquals. Prop2 ::= Term "=" Term ;
  PNot. Prop1 ::= "¬" Prop1 ;
  PAnd. Prop ::= Prop1 "∧" Prop ;
  PImpl. Prop ::= Prop1 "⇒" Prop ;
  PForall. Prop ::= "∀" Ident ":" RType "." Prop ;

  coercions Prop 2 ;

  TId. TacExpr1 ::= "id" ;
  TDone. TacExpr1 ::= "done" ;
  TInd. TacExpr1 ::= "by" "induction" "on" Ident ":" Prop ;
  TIntros. TacExpr1 ::= "intros" ;
  THave. TacExpr1 ::= "have" Prop "using" [Ident] ;
  TUse. TacExpr1 ::= "use" Ident "with" [Term1] ;
  TSUse. TacExpr1 ::= "use" Ident ;
  TThen. TacExpr ::= TacExpr1 ";" TacExpr ;
  TDispatch. TacExpr ::= TacExpr1 ";" TacAlt ;

  coercions TacExpr 2 ;

  separator Ident "," ;
  separator TacExpr "|" ;

  TacAlt. TacAlt ::= "[" [TacExpr] "]" ;

  JustTacAlt. MaybeTacAlt ::= TacAlt ;
  NothingTacAlt. MaybeTacAlt ::= ;

  Definition. Decl ::= "def" Ident ":" RType ;
  Axiom. Decl ::= "ax" Ident ":" Prop ;
  Theorem. Decl ::= "thm" Ident ":" Prop MaybeTacAlt;

  []. [Decl] ::= ;
  (:). [Decl] ::= Decl [Decl] ;

  Prog. Prog ::= [Decl] ;

  entrypoints Prog, Prop, RType, IType, Term, TacExpr, MaybeTacAlt
|]
