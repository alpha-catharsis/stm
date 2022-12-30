---------------------
-- Module declaration
---------------------

module Stm.Data.Stm.Stm

------------------------------
-- State transition definition
------------------------------

public export
Trans : Type -> Type -> Type
Trans s e = s -> e -> s -> Type

--------------------------
-- State machine interface
--------------------------

public export
interface Stm (0 s : Type) (0 e : Type) (0 tr : Trans s e) | tr where
  transFunct : {s1 : s} -> {ev : e} -> {s2 : s} -> {s2' : s} ->
               tr s1 ev s2 -> tr s1 ev s2' -> s2 = s2'
