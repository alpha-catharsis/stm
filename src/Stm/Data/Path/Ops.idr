---------------------
-- Module declaration
---------------------

module Stm.Data.Path.Ops

-------------------
-- External imports
-------------------

import Data.DPair
import Data.Nat

-------------------
-- Internal imports
-------------------

import Stm.Data.Step.Step
import Stm.Data.Stm.Stm
import Stm.Data.Path.Elem
import Stm.Data.Path.Path

---------------
-- Path joining
---------------

export
join : Path tr k s1 s2 -> Path tr k' s2 s3 -> Path tr (k + k') s1 s3
join pt12 (PathSingl _ stp23) = rewrite plusCommutative k 1 in
                                rewrite plusOneSucc k in PathNext pt12 stp23
join pt12 (PathNext pt24 stp43 {k=j}) = rewrite sym (plusSuccRightSucc k j)
                                        in PathNext (join pt12 pt24) stp43

-----------------
-- Path splitting
-----------------

export
splitUpTo : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
            {0 s1 : s} -> {0 s3 : s} ->
            (pt : Path tr k s1 s3) -> (s2 : s) -> (Elem s2 pt) ->
            Maybe (Exists (\k' => Path tr k' s1 s2))
splitUpTo (PathSingl s1 _) s1 InSingl1 = Nothing
splitUpTo (PathSingl s1 (MkStep tr _ ev s2 trPrf)) s2 InSingl2 =
  Just (Evidence _ (PathSingl s1 (MkStep tr s1 ev s2 trPrf)))
splitUpTo (PathNext pt14 (MkStep tr s4 ev s2 trPrf)) s2 InNext =
  Just (Evidence _ (PathNext pt14 (MkStep tr s4 ev s2 trPrf)))
splitUpTo (PathNext pt14 stp43) s2 (InPrev elemPrf) =
  splitUpTo pt14 s2 elemPrf

export
splitFromOn : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
              {0 s1 : s} -> {0 s3 : s} ->
              (pt : Path tr k s1 s3) -> (s2 : s) -> (Elem s2 pt) ->
              Maybe (Exists (\k' => Path tr k' s2 s3))
splitFromOn (PathSingl s1 stp13) s1 InSingl1 =
  Just (Evidence _ (PathSingl s1 stp13))
splitFromOn (PathSingl _ (MkStep _ _ _ s2 _)) s2 InSingl2 = Nothing
splitFromOn (PathNext _ (MkStep _ _ _ s2 _)) s2 InNext = Nothing
splitFromOn (PathNext (PathSingl s1 (MkStep tr s1 ev s2 trPrf)) stp23) s2
            (InPrev InSingl2) = Just (Evidence _ (PathSingl s2 stp23))
splitFromOn (PathNext (PathNext pt14 (MkStep tr s4 ev s2 trPrf)) stp23) s2
            (InPrev InNext) = Just (Evidence _ (PathSingl s2 stp23))
splitFromOn (PathNext pt14 stp43) s2 (InPrev elemPrf) =
  case splitFromOn pt14 s2 elemPrf of
    Nothing => Nothing
    Just (Evidence k pt24) => Just (Evidence (S k) (PathNext pt24 stp43))

-----------------
-- Path extension
-----------------

export
extendStart : Path tr k s2 s3 -> (s1 : s) -> Step tr s1 s2 ->
              Path tr (S k) s1 s3
extendStart pt23 s1 stp12 = join (PathSingl s1 stp12) pt23

export
extendEnd : Path tr k s1 s2 -> Step tr s2 s3 -> Path tr (S k) s1 s3
extendEnd pt12 stp23 = PathNext pt12 stp23

-----------------
-- Path reduction
-----------------

export
reduceStart : (pt13 : Path tr (S (S k)) s1 s3) ->
              Exists (\s2 => Path tr (S k) s2 s3)
reduceStart (PathSingl _ _) impossible
reduceStart (PathNext (PathSingl s1 stp12) stp23) =
  let Element s2' prf = end stp12
  in Evidence s2' (PathSingl s2' (rewrite prf in stp23))
reduceStart (PathNext (PathNext (PathSingl s1 stp14) stp42) stp23) =
  let Element s4 prf = end stp14
  in  Evidence s4 (PathNext (PathSingl s4 (rewrite prf in stp42)) stp23)
reduceStart (PathNext (PathNext (PathNext pt15 stp54) stp42) stp23) =
  let Evidence s6 pt62 = reduceStart (PathNext (PathNext pt15 stp54) stp42)
  in Evidence s6 (PathNext pt62 stp23)

export
reduceEnd : (pt13 : Path tr (S (S k)) s1 s3) ->
            Exists (\s2 => Path tr (S k) s1 s2)
reduceEnd (PathSingl _ _) impossible
reduceEnd (PathNext (PathSingl s1 stp12) stp23) =
  let Element s2 prf = end stp12
  in Evidence s2 (PathSingl s1 (rewrite prf in stp12))
reduceEnd (PathNext (PathNext pt14 stp42) stp23) =
  let Element s2 prf = end stp42
  in Evidence s2 (PathNext pt14 (rewrite prf in stp42))
