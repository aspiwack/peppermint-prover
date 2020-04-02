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
  Var. Term1 ::= Ident ;
  App. Term ::= Term Term1 ;

  coercions Term 3 ;

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

  Definition. Decl ::= "def" Ident ":" RType ;
  Axiom. Decl ::= "ax" Prop ;

  []. [Decl] ::= ;
  (:). [Decl] ::= Decl [Decl] ;

  Prog. Prog ::= [Decl] ;

  entrypoints Prog, Prop, RType, IType, Term
|]
