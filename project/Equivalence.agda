open import Data.Empty
open import Data.Unit
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Bool
open import Relation.Binary.PropositionalEquality renaming ([_] to [_]')
open import Relation.Binary
open import Relation.Nullary
import RegExp
import Automaton
import Compile

module Equivalence (Symbol : Set) (eq : Decidable {A = Symbol} _≡_) where

  open RegExp Symbol
  open Automaton Symbol
  open Compile Symbol eq
  open NFA

  regexp-nfa : ∀ {r : RegExpr} {w : List Symbol} → Match r w → Accept (compile r) [ start (compile r) ] w
  regexp-nfa match-ε = {!!}

  regexp-nfa (match-^ {a}) with eq a a | inspect (eq a) a
  ... | yes p | [ ξ ]' = accept-∷ (accept-[] {!ξ!} {!!})
  ... | no q | foo =  ⊥-elim (q refl)

  regexp-nfa (match-⊕-l p) = {!!}
  regexp-nfa (match-⊕-r p) = {!!}

  regexp-nfa (match-∙ p q) = {!!}

  regexp-nfa match-*-[] = {!!}
  regexp-nfa (match-*-++ p q) = {!!}

  nfa-regexp : ∀ (r : RegExpr) (w : List Symbol) → NFA.Accept (compile r) [ NFA.start (compile r) ] w → Match r w
  nfa-regexp r w p = {!!}
