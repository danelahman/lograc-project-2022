module proj where 


open import Data.Fin renaming (zero to zero'; suc to suc'; _+_ to _+'_)
open import Data.Nat
open import Data.List
open import Data.Bool

-- https://agda.readthedocs.io/en/v2.6.1/language/sized-types.html

variable
    n : ℕ
    m : ℕ

-- n Alphabet
-- Fin n Char
-- List (Fin n) String

Alphabet : Set 
Alphabet = ℕ

_⋆ₛ : Alphabet → Set -- set of all strings 
Σ ⋆ₛ = List Alphabet

data RegExpr : Set where
  ⊘ : RegExpr
  ε : RegExpr
  _^ : Alphabet → RegExpr
  _∪_ : RegExpr → RegExpr → RegExpr -- unija
  _●_ : RegExpr → RegExpr → RegExpr -- concat, cib
  _✹ : RegExpr → RegExpr -- st12

data _↠_ : List Alphabet → RegExpr → Set where -- rr-
  to-ε : [] ↠ ε -- empty string to empty regexp
  char-to-^ : {c : Alphabet} → [ c ] ↠ (c ^)
  to-∪-l : {s : List Alphabet} {exp₁ exp₂ : RegExpr} → s ↠ exp₁ → s ↠ (exp₁ ∪ exp₂) -- if s in exp₁ then s in (exp₁ ∪ exp₂)
  to-∪-r : {s : List Alphabet} {exp₁ exp₂ : RegExpr} → s ↠ exp₂ → s ↠ (exp₁ ∪ exp₂) -- if s in exp₁ then s in (exp₁ ∪ exp₂)
  to-● : {s₁ s₂ : List Alphabet} {exp₁ exp₂ : RegExpr} → s₁ ↠ exp₁ → s₂ ↠ exp₂ → (s₁ ++ s₂) ↠ (exp₁ ● exp₂)
  []-to-✹ : {exp : RegExpr} → [] ↠ (exp ✹) -- empty Fin n is always in kleen star
  to-✹ : {s₁ s₂ : List Alphabet} {exp : RegExpr} → s₁ ↠ exp → s₂ ↠ (exp ✹) → (s₂ ++ s₁) ↠ (exp ✹) -- In kleen star ✹ we have at least empty string ε. If we concat some string a with ε we get a in ✹, so we can get aa, aaa, ...
  
{- 
data RegExpr : Set where
  ⊘ : RegExpr
  ε : RegExpr
  _^ : Fin n → RegExpr
  _∪_ : RegExpr → RegExpr → RegExpr -- unija
  _●_ : RegExpr → RegExpr → RegExpr -- concat, cib
  _✹ : RegExpr → RegExpr -- st12

data _↠_ : List (Fin n) → RegExpr → Set where -- rr-
  -- to-ε : [] ↠ ε -- empty string to empty regexp
  char-to-^ : {c : Fin n} → [ c ] ↠ (c ^)
  to-∪-l : {s : List (Fin n)} {exp₁ exp₂ : RegExpr} → s ↠ exp₁ → s ↠ (exp₁ ∪ exp₂) -- if s in exp₁ then s in (exp₁ ∪ exp₂)
  to-∪-r : {s : List (Fin n)} {exp₁ exp₂ : RegExpr} → s ↠ exp₂ → s ↠ (exp₁ ∪ exp₂) -- if s in exp₁ then s in (exp₁ ∪ exp₂)
  to-● : {s₁ s₂ : List (Fin n)} {exp₁ exp₂ : RegExpr} → s₁ ↠ exp₁ → s₂ ↠ exp₂ → (s₁ ++ s₂) ↠ (exp₁ ● exp₂)
  -- []-to-✹ : {exp : RegExpr} → [] ↠ (exp ✹) -- empty Fin n is always in kleen star
  to-✹ : {s₁ s₂ : List (Fin n)} {exp : RegExpr} → s₁ ↠ exp → s₂ ↠ (exp ✹) → (s₁ ++ s₂) ↠ (exp ✹) -- In kleen star ✹ we have at least empty string ε. If we concat some string a with ε we get a in ✹, so we can get aa, aaa, ...
-}
