{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Empty
open import Data.Unit
open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Relation.Nullary

import RegExp
import Automaton
import 1-Symbol
import EmptySet
import EmptySymbol
import Sequence

module Compile (Symbol : Set) (eq : Decidable {A = Symbol} _≡_) where

  open RegExp Symbol
  open Automaton Symbol

  compile : RegExpr → NFA
  compile ⊘ = EmptySet.emptySet Symbol
  compile ε = EmptySymbol.emptySymbol Symbol
  compile (a ^) = 1-Symbol.1-symbol Symbol eq a
  compile (r₁ ⊕ r₂) = Sequence.sequence Symbol (compile r₁) (compile r₂)
  compile (r₁ ∙ r₂) = {!!}
  compile (r *) = {!!}
