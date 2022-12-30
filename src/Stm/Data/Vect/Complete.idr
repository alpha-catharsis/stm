---------------------
-- Module declaration
---------------------

module Stm.Data.Vect.Complete

-------------------
-- External imports
-------------------

import Data.Vect
import Data.Vect.Elem

------------------
-- Complete vector
------------------

public export
data Complete : {0 k : Nat} -> {0 t : Type} -> (v : Vect k t) -> Type where
  Compl : ((x : t) -> Elem x v) -> Complete v

