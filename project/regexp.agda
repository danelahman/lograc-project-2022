module regexp where

open import Data.Nat
open import Data.Fin renaming (zero to zero'; suc to suc'; _+_ to _+'_)
open import Data.List

Σ : ℕ → Set
Σ n = Fin n

data String Σ n : Set where
    ε : String Σ
    _::_ : Σ  

string : {n : ℕ} → List Σ n → Set
string sequence = ?

