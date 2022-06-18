open import Data.List
open import Data.List.Membership.Propositional
open import Data.Empty
open import Data.Unit
open import Data.Bool

module Automaton (Symbol : Set) where

  Word = List Symbol

  record NFA : Set₁ where
    field
      State : Set                         -- the type of states
      start : State                       -- starting state
      next : Symbol → State → List State  -- transition function
      accept : State → Bool               -- is it an accepting state?

    nexts : Symbol → List State → List State
    nexts a ss = concat (map (next a) ss)

    data Accept : List State → Word → Set where
      accept-[] : ∀ {ss : List State} {s : State} → s ∈ ss → T (accept s) → Accept ss []
      accept-∷ : ∀ {ss : List State} {a : Symbol} {w : Word} → Accept (nexts a ss) w → Accept ss (a ∷ w)
