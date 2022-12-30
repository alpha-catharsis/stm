---------------------
-- Module declaration
---------------------

module Stm.Example.Semaphore

-------------------
-- External imports
-------------------

import Data.Vect
import Data.Vect.Elem

-------------------
-- Internal imports
-------------------

import Stm.Data

-----------------------------
-- Semaphore state definition
-----------------------------

public export
data Sem : Type where
  Green : Sem
  Yellow : Sem
  Red : Sem
  Black : Sem

--------------------------------------
-- Semaphore state Enumerable instance
--------------------------------------

public export
Enumerable 4 Sem where
  enumerated = [Green, Yellow, Red, Black]

  enumeratedAll = Compl $ \case
    Green => Here
    Yellow => There Here
    Red => There (There Here)
    Black => There (There (There Here))

  enumeratedUnique = NoDupCons Green _ (\case
      Here impossible
      There later => case later of
        Here impossible
        There later' => case later' of
          Here impossible
          There _ impossible)
    (NoDupCons Yellow _ (\case
        Here impossible
        There later => case later of
          Here impossible
          There _ impossible)
      (NoDupCons Red _ (\case
          Here impossible
          There _ impossible)
        (NoDupCons Black _ absurd NoDupNil)))

-----------------------------
-- Semaphore event definition
-----------------------------

public export
data Ev : Type where
  Stop : Ev
  Next : Ev
  Fail : Ev

--------------------------------------
-- Semaphore event Enumerable instance
--------------------------------------

public export
Enumerable 3 Ev where
  enumerated = [Stop, Next, Fail]

  enumeratedAll = Compl $ \case
    Stop => Here
    Next => There Here
    Fail => There (There Here)

  enumeratedUnique = NoDupCons Stop _ (\case
        Here impossible
        There later => case later of
          Here impossible
          There _ impossible)
      (NoDupCons Next _ (\case
          Here impossible
          There _ impossible)
        (NoDupCons Fail _ absurd NoDupNil))

------------------------------
-- Semaphore state transitions
------------------------------

public export
data SemTrans : Trans Sem Ev where
  GreenStop : SemTrans Green Stop Green
  GreenNext : SemTrans Green Next Yellow
  GreenFail : SemTrans Green Fail Black
  YellowNext : SemTrans Yellow Next Red
  YellowFail : SemTrans Yellow Fail Black
  RedStop : SemTrans Red Stop Red
  RedNext : SemTrans Red Next Green
  RedFail : SemTrans Red Fail Black

-------------------------
-- Semaphore Stm instance
-------------------------

public export
Stm Sem Ev SemTrans where
  transFunct GreenStop GreenStop = Refl
  transFunct GreenNext GreenNext = Refl
  transFunct GreenFail GreenFail = Refl
  transFunct YellowNext YellowNext = Refl
  transFunct YellowFail YellowFail = Refl
  transFunct RedStop RedStop = Refl
  transFunct RedNext RedNext = Refl
  transFunct RedFail RedFail = Refl
