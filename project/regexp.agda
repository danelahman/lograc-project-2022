module regexp where

open import Data.Nat
open import Data.Fin renaming (zero to zero'; suc to suc'; _+_ to _+'_)
open import Data.List


    

Alphabet : Set
Alphabet = ℕ

String : Set
String = {Σ : Alphabet} → List(Fin Σ)

--set of all strings
_⋆ : Alphabet → Set
Σ ⋆ = List (Fin Σ)

data RegExpr : Set where
  ε : RegExpr
  _^ : Alphabet → RegExpr
  _∪_ : RegExpr → RegExpr → RegExpr -- unija
  _●_ : RegExpr → RegExpr → RegExpr -- concat, cib
  _✹ : RegExpr → RegExpr -- st12


data _↠_ : String → RegExpr → Set where -- rr-
  empty : [] ↠ ε
  -- char : {c : Alphabet} → ([ c ⋆ ]) ↠ (c ^)


{-
data Σ : ℕ → Set where
  ∅     : Σ zero
  letter  : (i : Σ n) → Σ (suc n)


  ⭑
-}

{-
data String : {n : ℕ} → Σ n → Set where
    ε : {!   !}
-}

{-
data String (l : Σ n) : Set where
  ε  : String ∅
  _·_ : l → String l → String l
-}

{-
    string : {n : ℕ} → List Σ n
    string sequence = ?
-}
