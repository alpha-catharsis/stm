---------------------
-- Module declaration
---------------------

module Stm.Data.Path.Elem

-------------------
-- External imports
-------------------

import Decidable.Decidable
import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Stm.Data.Path.Path
import Stm.Data.Step.Step
import Stm.Data.Stm.Stm

---------------
-- Path element
---------------

public export
data Elem : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
            {0 s1 : s} -> {0 s2 : s} -> s -> Path tr k s1 s2 -> Type where
  InSingl1 : Elem s1 (PathSingl s1 _)
  InSingl2 : Elem s2 (PathSingl _ (MkStep _ _ _ s2 _))
  InNext : Elem s2 (PathNext _ (MkStep _ _ _ s2 _))
  InPrev : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
           {0 s1 : s} -> {0 s2 : s} -> {0 s3 : s} ->
           {0 stp23 : Step tr s2 s3} -> {0 sx : s} ->
           {0 pt12 : Path tr k s1 s2} -> Elem sx pt12 ->
           Elem sx (PathNext pt12 stp23)

------------------------
-- Path element decision
------------------------

noElemInSingl : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
               (sx : s) -> (s1 : s) -> (s2 : s) ->
               {0 stp12 : Step tr s1 s2} -> Not (sx = s1) -> Not (sx = s2) ->
               Not (Elem sx (PathSingl s1 stp12))
noElemInSingl s1 s1 _ contra1 _ InSingl1 = contra1 Refl
noElemInSingl s2 _ s2 _ contra2 InSingl2 = contra2 Refl

noElemInNextOrPrev : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
                     (sx : s) -> {0 s1 : s} -> {0 s2 : s} ->
                     {0 pt12 : Path tr k s1 s2} -> (s3 : s) ->
                     {0 stp23 : Step tr s2 s3} ->
                     Not (sx = s3) -> Not (Elem sx pt12) ->
                     Not (Elem sx (PathNext pt12 stp23))
noElemInNextOrPrev s3 s3 eqContra _ InNext =
  eqContra Refl
noElemInNextOrPrev _ _ _ prevContra (InPrev prevPrf) =
  prevContra prevPrf

export
decElem : DecEq s => (sx : s) -> (pt : Path tr k s1 s2) -> Dec (Elem sx pt)
decElem sx (PathSingl s1 (MkStep _ _ _ s2 _)) = case decEq sx s1 of
  Yes eqPrf1 => Yes (rewrite eqPrf1 in InSingl1)
  No eqContra1 => case decEq sx s2 of
    No eqContra2 => No (noElemInSingl sx s1 s2 eqContra1 eqContra2)
    Yes eqPrf2 => Yes (rewrite eqPrf2 in InSingl2)
decElem sx (PathNext pt12 (MkStep _ _ _ s3 _)) = case decEq sx s3 of
  Yes eqPrf => Yes (rewrite eqPrf in InNext)
  No eqContra => case decElem sx pt12 of
    No prevContra => No (noElemInNextOrPrev sx s3 eqContra prevContra)
    Yes prevPrf => Yes (InPrev prevPrf)
