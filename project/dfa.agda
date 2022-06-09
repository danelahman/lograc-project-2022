module dfa where -- (Σ : Set) where
open import Data.Nat as ℕ using (ℕ)
open import Data.Bool using (T; Bool; true; false; if_then_else_; _∧_)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Fin.Subset as Subset using (Subset)
open import Data.Fin.Subset using (⋃; ⁅_⁆)
open import Data.List.Base using (map)
open import Data.List
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Nat as ℕ using (ℕ; _≟_; zero; suc)
open import Data.Fin renaming (_≟_ to _≟ᶠ_)
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_)
-- open import Data.String Σ using (String; []; _∷_)

a = 0
b = 1
c = 2
d = 3

Σ = ℕ

record DFA ( n : ℕ) : Set where
    field
        S : Fin n               -- start state
        δ : Fin n → Σ → Fin n   -- transition function
        F : Subset n            -- end state


open DFA

TransitionsList = λ n → List (Fin n × Σ × Fin n)

make-δ : ∀{n}
    → Fin n -- error state
    → TransitionsList n -- a list of possible transitions
    → (Fin n → Σ → Fin n )  -- func from current state and current letter to new state
make-δ err [] = λ  _ _ → err
make-δ err ((q , x , p) ∷ xs) 
    = λ h y → if ⌊ q ≟ᶠ h ⌋ ∧ ⌊ x ≟ y ⌋
              then p
              else make-δ err xs h y

make-dfa : (n : ℕ)
        → Fin n  -- start state
        → Fin n  -- error state
        → List (Fin n) -- list of end (accepting) states
        → TransitionsList n -- list of transitions
        → DFA n
make-dfa n qₛ qₑ Q_f trans
    = record
        {
            S = qₛ ;
            δ = make-δ qₑ trans ;
            F = ⋃ (map ⁅_⁆ Q_f)
        }




        
δd* : ∀{n} → DFA n → Fin n → List Σ → Fin n
δd* A q [] = q
δd* A q (x ∷ xs) = δd* A (δ A q x) xs 