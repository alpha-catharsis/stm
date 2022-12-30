---------------------
-- Module declaration
---------------------

module Stm.Data.Vect.NoDup

-------------------
-- External imports
-------------------

import Data.Vect
import Data.Vect.Elem

----------------------------
-- Vector without duplicates
----------------------------

public export
data NoDup : {0 k : Nat} -> {0 t : Type} -> Vect k t -> Type where
  NoDupNil : NoDup []
  NoDupCons : (x : t) -> (v : Vect k t) -> Not (Elem x v) -> NoDup v ->
              NoDup (x :: v)
