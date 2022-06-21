open import Data.List
open import Data.Bool
open import Relation.Binary

import Automaton

module EmptySymbol (Symbol : Set) where

  open Automaton Symbol
  open NFA

  data Empty-State : Set where
    state-accept : Empty-State
    state-reject : Empty-State

  emptySymbol : NFA
  emptySymbol =
      record
        { State = Empty-State
        ; start = state-accept
        ; next = λ { b state-accept → [ state-reject ]
                   ; b state-reject → [ state-reject ]
                   }
        ; accept = λ { state-accept → true
                     ; state-reject → false}
        }
