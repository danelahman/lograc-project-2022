open import Data.Nat as ℕ using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Subset as Subset using (Subset)
module dfa (Σ : Set) where

record DFA ( n : ℕ) : Set where
    field
        S : Fin n               -- start state
        δ : Fin n → Σ → Fin n   -- transition function
        F : Subset n            -- end state

