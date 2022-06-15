module RegExp where 


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

-- Alphabet : Set 
-- Alphabet = ℕ


-- data RegExpr : Set where
--   ⊘ : RegExpr
--   ε : RegExpr
--   _^ : Alphabet → RegExpr
--   _∪_ : RegExpr → RegExpr → RegExpr -- unija
--   _●_ : RegExpr → RegExpr → RegExpr -- concat, cib
--   _✹ : RegExpr → RegExpr -- st12

-- data _↠_ : List Alphabet → RegExpr → Set where -- rr-
--   to-ε : [] ↠ ε -- empty string to empty regexp
--   char-to-^ : {c : Alphabet} → [ c ] ↠ (c ^)
--   to-∪-l : {s : List Alphabet} {exp₁ exp₂ : RegExpr} → s ↠ exp₁ → s ↠ (exp₁ ∪ exp₂) -- if s in exp₁ then s in (exp₁ ∪ exp₂)
--   to-∪-r : {s : List Alphabet} {exp₁ exp₂ : RegExpr} → s ↠ exp₂ → s ↠ (exp₁ ∪ exp₂) -- if s in exp₁ then s in (exp₁ ∪ exp₂)
--   to-● : {s₁ s₂ : List Alphabet} {exp₁ exp₂ : RegExpr} → s₁ ↠ exp₁ → s₂ ↠ exp₂ → (s₁ ++ s₂) ↠ (exp₁ ● exp₂)
--   []-to-✹ : {exp : RegExpr} → [] ↠ (exp ✹) -- empty Fin n is always in kleen star
--   to-✹ : {s₁ s₂ : List Alphabet} {exp : RegExpr} → s₁ ↠ exp → s₂ ↠ (exp ✹) → (s₂ ++ s₁) ↠ (exp ✹) -- In kleen star ✹ we have at least empty string ε. If we concat some string a with ε we get a in ✹, so we can get aa, aaa, ...
  
 
data RegExpr : Set where
  ⊘ : RegExpr
  ε : RegExpr
  _^ : Fin n → RegExpr
  _+ᵣ_ : RegExpr → RegExpr → RegExpr -- union
  _∙_ : RegExpr → RegExpr → RegExpr -- concatination
  _* : RegExpr → RegExpr -- Kleene star

data _↠_ : List (Fin n) → RegExpr → Set where -- rr-
  to-ε : [] ↠ ε -- empty string to empty regexp
  char-to-^ : {c : Fin n} → [ c ] ↠ (c ^)
  to-+ᵣ-l : {s : List (Fin n)} {exp₁ exp₂ : RegExpr} → s ↠ exp₁ → s ↠ (exp₁ +ᵣ exp₂) -- if s in exp₁ then s in (exp₁ +ᵣ exp₂)
  to-+ᵣ-r : {s : List (Fin n)} {exp₁ exp₂ : RegExpr} → s ↠ exp₂ → s ↠ (exp₁ +ᵣ exp₂) -- if s in exp₁ then s in (exp₁ +ᵣ exp₂)
  to-∙ : {s₁ s₂ : List (Fin n)} {exp₁ exp₂ : RegExpr} → s₁ ↠ exp₁ → s₂ ↠ exp₂ → (s₁ ++ s₂) ↠ (exp₁ ∙ exp₂)
  []-to-* : {exp : RegExpr} → [] ↠ (exp *) -- empty Fin n is always in Kleene star
  to-* : {s₁ s₂ : List (Fin n)} {exp : RegExpr} → s₁ ↠ exp → s₂ ↠ (exp *) → (s₁ ++ s₂) ↠ (exp *) -- In Kleene star ✹ we have at least empty string ε. If we concat some string a with ε we get a in ✹, so we can get aa, aaa, ...

