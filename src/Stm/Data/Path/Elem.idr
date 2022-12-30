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
            {0 s1 : s} -> {0 s2 : s} -> s -> Path tr s1 s2 -> Type where
  InSingl : Elem s1 (PathSingl s1 _)
  InNext : Elem s2 (PathNext _ (MkStep _ _ _ s2 _))
  InPrev : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
           {0 s1 : s} -> {0 s2 : s} -> {0 s3 : s} ->
           {0 stp23 : Step tr s2 s3} -> {0 sx : s} ->
           {0 pt12 : Path tr s1 s2} -> Elem sx pt12 ->
           Elem sx (PathNext pt12 stp23)

------------------------
-- Path element decision
------------------------

noElemInSingl : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
                (sx : s) -> (s1 : s) -> {0 s2 : s} ->
                {0 stp12 : Step tr s1 s2} -> Not (sx = s1) ->
                Not (Elem sx (PathSingl s1 stp12))
noElemInSingl s1 s1 contra InSingl = contra Refl

noElemInNextOrPrev : {0 s : Type} -> {0 e : Type} -> {0 tr : Trans s e} ->
                     (sx : s) -> {0 s1 : s} -> {0 s2 : s} ->
                     {0 pt12 : Path tr s1 s2} -> (s3 : s) ->
                     {0 stp23 : Step tr s2 s3} ->
                     Not (sx = s3) -> Not (Elem sx pt12) ->
                     Not (Elem sx (PathNext pt12 stp23))
noElemInNextOrPrev s3 s3 eqContra _ InNext =
  eqContra Refl
noElemInNextOrPrev _ _ _ prevContra (InPrev prevPrf) =
  prevContra prevPrf

export
decElem : DecEq s => (sx : s) -> (pt : Path tr s1 s2) -> Dec (Elem sx pt)
decElem sx (PathSingl s1 stp12) = case decEq sx s1 of
  No eqContra => No (noElemInSingl sx s1 eqContra)
  Yes eqPrf => Yes (rewrite eqPrf in InSingl)
decElem sx (PathNext pt12 (MkStep _ _ _ s3 _)) = case decEq sx s3 of
  Yes eqPrf => Yes (rewrite eqPrf in InNext)
  No eqContra => case decElem sx pt12 of
    No prevContra => No (noElemInNextOrPrev sx s3 eqContra prevContra)
    Yes prevPrf => Yes (InPrev prevPrf)
