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
  enumeratedAll : Complete enumerated
  enumeratedUnique : NoDup enumerated

-----------------------
-- Enumerable functions
-----------------------

export
finToEnum : Enumerable k e => Fin k -> e
finToEnum idx = index idx enumerated

export
enumToFin : Enumerable k e => e -> Fin k
enumToFin x = completeIdx enumeratedAll x
