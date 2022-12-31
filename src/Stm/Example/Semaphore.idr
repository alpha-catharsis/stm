---------------------
-- Module declaration
---------------------

module Stm.Example.Semaphore

-------------------
-- External imports
-------------------

import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

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

---------------------------------
-- Semaphore state DecEq instance
---------------------------------

public export
DecEq Sem where
  decEq Green Green = Yes Refl
  decEq Green Yellow = No (\prf => case prf of _ impossible)
  decEq Green Red = No (\prf => case prf of _ impossible)
  decEq Green Black = No (\prf => case prf of _ impossible)
  decEq Yellow Green = No (\prf => case prf of _ impossible)
  decEq Yellow Yellow = Yes Refl
  decEq Yellow Red = No (\prf => case prf of _ impossible)
  decEq Yellow Black = No (\prf => case prf of _ impossible)
  decEq Red Green = No (\prf => case prf of _ impossible)
  decEq Red Yellow = No (\prf => case prf of _ impossible)
  decEq Red Red = Yes Refl
  decEq Red Black = No (\prf => case prf of _ impossible)
  decEq Black Green = No (\prf => case prf of _ impossible)
  decEq Black Yellow = No (\prf => case prf of _ impossible)
  decEq Black Red = No (\prf => case prf of _ impossible)
  decEq Black Black = Yes Refl

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

---------------------------------
-- Semaphore event DecEq instance
---------------------------------

public export
DecEq Ev where
  decEq Stop Stop = Yes Refl
  decEq Stop Next = No (\prf => case prf of _ impossible)
  decEq Stop Fail = No (\prf => case prf of _ impossible)
  decEq Next Stop = No (\prf => case prf of _ impossible)
  decEq Next Next = Yes Refl
  decEq Next Fail = No (\prf => case prf of _ impossible)
  decEq Fail Stop = No (\prf => case prf of _ impossible)
  decEq Fail Next = No (\prf => case prf of _ impossible)
  decEq Fail Fail = Yes Refl

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

-------------------------
-- Semaphore path example
-------------------------

export
semPath1 : Path SemTrans 3 Green Green
semPath1 = PathNext (PathNext (PathSingl Green
                                         (MkStep SemTrans _ _ _ GreenNext))
                              (MkStep SemTrans _ _ _YellowNext))
                    (MkStep SemTrans _ _ _ RedNext)

export
semPath2 : Path SemTrans 3 Green Black
semPath2 = PathNext (PathNext (PathSingl Green
                                         (MkStep SemTrans _ _ _ GreenNext))
                              (MkStep SemTrans _ _ _YellowNext))
                    (MkStep SemTrans _ _ _ RedFail)

export
green1InPath1 : Path.Elem.Elem Green Semaphore.semPath1
green1InPath1 = InPrev (InPrev InSingl1)

export
yellowInPath1 : Path.Elem.Elem Yellow Semaphore.semPath1
yellowInPath1 = InPrev (InPrev InSingl2)

export
redInPath1 : Path.Elem.Elem Red Semaphore.semPath1
redInPath1 = InPrev InNext

export
green2InPath1 : Path.Elem.Elem Green Semaphore.semPath1
green2InPath1 = InNext

export
greenInPath2 : Path.Elem.Elem Green Semaphore.semPath2
greenInPath2 = InPrev (InPrev InSingl1)

export
yellowInPath2 : Path.Elem.Elem Yellow Semaphore.semPath2
yellowInPath2 = InPrev (InPrev InSingl2)

export
redInPath2 : Path.Elem.Elem Red Semaphore.semPath2
redInPath2 = InPrev InNext

export
blackInPath2 : Path.Elem.Elem Black Semaphore.semPath2
blackInPath2 = InNext
