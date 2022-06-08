module reglang where 

open import Data.Nat
open import Data.Fin renaming (zero to zero'; suc to suc'; _+_ to _+'_)
open import Data.List
open import Data.Bool

variable
    n : ℕ
    m : ℕ

Alphabet : Set
Alphabet = ℕ

String : Set
String = {Σ : Alphabet} → List (Fin Σ)


--set of all strings
_⋆ : Alphabet → Set
Σ ⋆ = List (Fin Σ)


data RegLang : Set where
    ∅ : RegLang
    <ε> : {!   !}
    <_> : {!   !}
    _∪ₗ_ : {!   !} 
    _·ₗ_ : {!   !}
    _*ₗ_ : {!   !}

{-
Language _ : List (fin n) -> boole
Language n = 
-}



data RegExpr : Set where
  ε : RegExpr
  _^ : Alphabet → RegExpr
  _∪_ : RegExpr → RegExpr → RegExpr -- unija
  _●_ : RegExpr → RegExpr → RegExpr -- concat, cib
  _✹ : RegExpr → RegExpr -- st12


data _↠_ : String → RegExpr → Set where -- rr-
  to-ε : [] ↠ ε -- empty string to empty regexp
  char-to-^ : {Σ : Alphabet} {c : Fin Σ} → [ {! c  !} ] ↠ ({!   !} ^)
  to-∪-l : {s : String} {exp₁ exp₂ : RegExpr} → s ↠ exp₁ → s ↠ (exp₁ ∪ exp₂) -- if s in exp₁ then s in (exp₁ ∪ exp₂)
  to-∪-r : {s : String} {exp₁ exp₂ : RegExpr} → s ↠ exp₂ → s ↠ (exp₁ ∪ exp₂) -- if s in exp₁ then s in (exp₁ ∪ exp₂)
  to-● : {s₁ s₂ : String} {exp₁ exp₂ : RegExpr} → s₁ ↠ exp₁ → s₂ ↠ exp₂ → (s₁ ++ s₂) ↠ (exp₁ ● exp₂)
  []-to-✹ : {exp : RegExpr} → [] ↠ (exp ✹) -- empty string is always in kleen star
  to-✹ : {s₁ s₂ : String} {exp : RegExpr} → s₁ ↠ exp → s₂ ↠ (exp ✹) → (s₁ ++ s₂) ↠ (exp ✹) -- In kleen star ✹ we have at least empty string ε. If we concat some string a with ε we get a in ✹, so we can get aa, aaa, ...
  