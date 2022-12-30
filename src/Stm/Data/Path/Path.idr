---------------------
-- Module declaration
---------------------

module Stm.Data.Path.Path

-------------------
-- External imports
-------------------

import Data.Nat

-------------------
-- Internal imports
-------------------

import Stm.Data.Step.Step
import Stm.Data.Stm.Stm

------------------
-- Path definition
------------------

public export
data Path : Trans s e -> s -> s -> Type where
  PathSingl : (s1 : s) -> Step tr s1 s2 -> Path tr s1 s2
  PathNext : Path tr s1 s2 -> Step tr s2 s3 -> Path tr s1 s3

---------------------
-- Path start and end
---------------------

pathStart : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
            {0 s1 : s} -> {0 s2 : s} ->
            Path tr s1 s2 -> (s1' : s ** s1' = s1)
pathStart (PathSingl s1 _) = (s1 ** Refl)
pathStart (PathNext pt _) = pathStart pt

pathEnd : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
          {0 s1 : s} -> {0 s2 : s} ->
          Path tr s1 s2 -> (s2' : s ** s2' = s2)
pathEnd (PathSingl _ stp) = stepEnd stp
pathEnd (PathNext _ stp) = stepEnd stp

--------------
-- Path length
--------------

pathLength : Path tr s1 s2 -> (k : Nat ** IsSucc k)
pathLength (PathSingl _ _) = (1 ** ItIsSucc)
pathLength (PathNext pt _) = let (k ** _) = pathLength pt in (S k ** ItIsSucc)
