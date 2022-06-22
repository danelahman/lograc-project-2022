open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum hiding (map)
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Relation.Nullary

import Automaton

module Parallel (Symbol : Set) where

  open Automaton Symbol
  open NFA

  data Parallel-State : Set where
    state-start : Parallel-State

  parallel : NFA → NFA → NFA
  parallel A B =
    record
      { State = Parallel-State ⊎ (State A ⊎ State B)  
      ; start =  inj₁ state-start
      ; next = λ { a (inj₁ _) → map inj₂ (concat (map inj₁ (next A a (start A)) ∷ map inj₂ (next B a (start B)) ∷ [])) -- We add state-start as start state and ε transitions to start of A and B. To get rid of ε tranzitions we make transitions state-start -(ε)→ start A -(simbol s)→ next with state-start -(simbol s)→ next
                 ; a (inj₂ (inj₁ s)) → map inj₂ (map inj₁ (next A a s))
                 ; a (inj₂ (inj₂ s)) → map inj₂ (map inj₂ (next B a s))}
      ; accept = λ {(inj₁ _) → false
                  ; (inj₂ (inj₁ s)) → accept A s
                  ; (inj₂ (inj₂ s)) → accept B s}
      }
   
 