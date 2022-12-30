---------------------
-- Module declaration
---------------------

module Stm.Data.Path.Ops

-------------------
-- Internal imports
-------------------

import Stm.Data.Step.Step
import Stm.Data.Stm.Stm
import Stm.Data.Path.Path
import Stm.Data.Path.Prop

---------------
-- Path joining
---------------

public export
path_join : Path tr s1 s2 -> Path tr s2 s3 -> Path tr s1 s3
path_join pt12 (PathSingl _ stp23) = PathNext pt12 stp23
path_join pt12 (PathNext pt24 stp43) = PathNext (path_join pt12 pt24) stp43

-----------------
-- Path reduction
-----------------

public export
path_retract_start : (pt13 : Path tr s1 s3) -> (0 cprf : CmplxPath pt13) ->
                     (s2 ** Path tr s2 s3)
path_retract_start (PathSingl _ _) (CmplxPath _) impossible
path_retract_start (PathNext (PathSingl s1 stp12) stp23) _ =
  let (s2 ** Refl) = step_end stp12 in (s2 ** PathSingl s2 stp23)
path_retract_start (PathNext (PathNext pt14 stp42) stp23) _ =
  let (s5 ** pt52) = path_retract_start
                     (assert_smaller (PathNext (PathNext pt14 stp42) stp23)
                                     (PathNext pt14 stp42))
                     (MkCmplxPath pt14 stp42)
  in (s5 ** PathNext pt52 stp23)

public export
path_retract_end : (pt13 : Path tr s1 s3) -> CmplxPath pt13 ->
                   (s2 ** Path tr s1 s2)
path_retract_end (PathSingl _ _) (CmplxPath _) impossible
path_retract_end (PathNext (PathSingl s1 stp12) stp23) _ =
  let (s2 ** Refl) = step_end stp12 in (s2 ** PathSingl s1 stp12)
path_retract_end (PathNext (PathNext pt14 stp42) stp23) _ =
  let (s2 ** Refl) = step_end stp42 in (s2 ** PathNext pt14 stp42)
