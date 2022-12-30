---------------------
-- Module declaration
---------------------

module Stm.Data.Enumerable

-------------------
-- External imports
-------------------

import Data.Vect
import Data.Vect.Elem

-------------------
-- Internal imports
-------------------

import Stm.Data.Vect.Complete
import Stm.Data.Vect.NoDup

----------------------------------
-- Enumerable interface definition
----------------------------------

public export
interface Enumerable (0 k : Nat) (0 t : Type) where
  enumerated : Vect k t
  enumerated_all : Complete enumerated
  enumerated_unique : NoDup enumerated
