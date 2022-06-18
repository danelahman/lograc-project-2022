open import Data.Fin renaming (zero to zero'; suc to suc'; _+_ to _+'_)
open import Data.Nat
open import Data.List
open import Data.Bool

module RegExp (Symbol : Set) where

data RegExpr : Set where
  ⊘ : RegExpr
  ε : RegExpr
  _^ : Symbol → RegExpr
  _⊕_ : RegExpr → RegExpr → RegExpr -- union
  _∙_ : RegExpr → RegExpr → RegExpr -- concatination
  _* : RegExpr → RegExpr -- Kleene star

Word : Set
Word = List Symbol

data Match : RegExpr → Word → Set where -- rr-
  match-ε : Match ε []
  match-^ : ∀ {a : Symbol} → Match (a ^) [ a ]
  match-⊕-l : ∀ {w : Word} {r₁ r₂ : RegExpr} → Match r₁ w → Match (r₁ ⊕ r₂) w
  match-⊕-r : ∀ {w : Word} {r₁ r₂ : RegExpr} → Match r₂ w → Match (r₁ ⊕ r₂) w
  match-∙ : ∀ {w₁ w₂ : Word} {r₁ r₂ : RegExpr} → Match r₁ w₁ → Match r₂ w₂ → Match (r₁ ∙ r₂) (w₁ ++ w₂)
  match-*-[] : ∀ {r : RegExpr} → Match (r *) []
  match-*-++ : ∀ {r : RegExpr} {w₁ w₂ : Word} → Match r w₁ → Match (r *) w₂ → Match (r *) (w₁ ++ w₂)
