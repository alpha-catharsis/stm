---------------------
-- Module declaration
---------------------

module Stm.Data.Path.Path

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

-----------------
-- Path functions
-----------------

path_start : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
             {0 s1 : s} -> {0 s2 : s} ->
             Path tr s1 s2 -> (s1' : s ** s1' = s1)
path_start (PathSingl s1 _) = (s1 ** Refl)
path_start (PathNext pt _) = path_start pt

path_end : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
             {0 s1 : s} -> {0 s2 : s} ->
             Path tr s1 s2 -> (s2' : s ** s2' = s2)
path_end (PathSingl _ stp) = step_end stp
path_end (PathNext _ stp) = step_end stp
