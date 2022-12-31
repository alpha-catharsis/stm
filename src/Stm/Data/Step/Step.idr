---------------------
-- Module declaration
---------------------

module Stm.Data.Step.Step

-------------------
-- External imports
-------------------

import Data.DPair

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
           (0 trPrf : tr s1 ev s2) -> Step tr s1 s2

-----------------
-- Step functions
-----------------

export
end : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
      {0 s1 : s} -> {0 s2 : s} -> Step tr s1 s2 ->
      Subset s (\s2' => s2' = s2)
end (MkStep _ _ _ s2 _) = Element s2 Refl

export
event : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
        {0 s1 : s} -> {0 s2 : s} -> Step tr s1 s2 ->
        Subset e (\ev => tr s1 ev s2)
event (MkStep _ _ ev _ trPrf) = Element ev trPrf

