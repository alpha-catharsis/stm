---------------------
-- Module declaration
---------------------

module Stm.Data.Path.Path

-------------------
-- External imports
-------------------

import Data.DPair
import Data.Fin
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
data Path : Trans s e -> Nat -> s -> s -> Type where
  PathSingl : (s1 : s) -> Step tr s1 s2 -> Path tr 1 s1 s2
  PathNext : Path tr k s1 s2 -> Step tr s2 s3 -> Path tr (S k) s1 s3

---------------------
-- Path start and end
---------------------

export
start : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
        {0 s1 : s} -> {0 s2 : s} ->
        Path tr k s1 s2 -> Subset s (\s1' => s1' = s1)
start (PathSingl s1 _) = Element s1 Refl
start (PathNext pt _) = start pt

export
end : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
      {0 s1 : s} -> {0 s2 : s} ->
      Path tr k s1 s2 -> Subset s (\s2' => s2' = s2)
end (PathSingl _ stp) = end stp
end (PathNext _ stp) = end stp

--------------
-- Path length
--------------

export
length : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
         {0 s1 : s} -> {0 s2 : s} ->
         Path tr k s1 s2 -> Subset Nat (\k' => k' = k)
length (PathSingl _ _) = Element 1 Refl
length (PathNext pt _) = let Element k eqPrf = length pt
                         in Element (S k) (cong S eqPrf)

-------------
-- Path state
-------------

export
checkLastIndex : {0 k : Nat} -> Path tr k s1 s2 -> Fin (S k) ->
                 Either (Fin (S k)) (Fin k)
checkLastIndex (PathSingl _ _) FZ = Right FZ
checkLastIndex (PathSingl _ _) (FS FZ) = Left (FS FZ)
checkLastIndex (PathNext pt _) FZ = Right FZ
checkLastIndex (PathNext pt _) (FS p) = case checkLastIndex pt p of
  Left idx => Left (FS idx)
  Right idx => Right (FS idx)

export
stateAt : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
          {0 s1 : s} -> {0 s2 : s} ->
          Path tr k s1 s2 -> (p : Fin (S k)) -> s
stateAt (PathSingl s1 _) FZ = s1
stateAt (PathSingl _ stp12) (FS FZ) = let Element s2 _ = end stp12 in s2
stateAt (PathNext pt12 stp12) p =
  case checkLastIndex (PathNext pt12 stp12) p of
    Left _ => let Element s2 _ = end stp12 in s2
    Right p' => stateAt pt12 p'
