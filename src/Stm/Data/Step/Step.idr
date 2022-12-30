---------------------
-- Module declaration
---------------------

module Stm.Data.Step.Step

-------------------
-- Internal imports
-------------------

import Stm.Data.Stm.Stm

------------------
-- Step definition
------------------

public export
data Step : Trans s e -> s -> s -> Type where
  MkStep : (0 tr : Trans s e) -> (0 s1 : s) -> (ev : e) -> (s2 : s) ->
           (0 trprf : tr s1 ev s2) -> Step tr s1 s2

-----------------
-- Step functions
-----------------

export
step_ev : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
          {0 s1 : s} -> {0 s2 : s} -> Step tr s1 s2 -> e
step_ev (MkStep _ _ ev _ _) = ev

export
step_end : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
          {0 s1 : s} -> {0 s2 : s} -> Step tr s1 s2 -> (s2' : s ** s2' = s2)
step_end (MkStep _ _ _ s2 _) = (s2 ** Refl)
