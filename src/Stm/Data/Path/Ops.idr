---------------------
-- Module declaration
---------------------

module Stm.Data.Path.Ops

-------------------
-- Internal imports
-------------------

import Stm.Data.Step.Step
import Stm.Data.Stm.Stm
import Stm.Data.Path.CmplxPath
import Stm.Data.Path.Elem
import Stm.Data.Path.Path

---------------
-- Path joining
---------------

export
pathJoin : Path tr s1 s2 -> Path tr s2 s3 -> Path tr s1 s3
pathJoin pt12 (PathSingl _ stp23) = PathNext pt12 stp23
pathJoin pt12 (PathNext pt24 stp43) = PathNext (pathJoin pt12 pt24) stp43

-----------------
-- Path reduction
-----------------

export
pathRetractStart : (pt13 : Path tr s1 s3) -> (0 cprf : CmplxPath pt13) ->
                     (s2 ** Path tr s2 s3)
pathRetractStart (PathSingl _ _) (CmplxPath _) impossible
pathRetractStart (PathNext (PathSingl s1 stp12) stp23) _ =
  let (s2 ** Refl) = stepEnd stp12 in (s2 ** PathSingl s2 stp23)
pathRetractStart (PathNext (PathNext pt14 stp42) stp23) _ =
  let (s5 ** pt52) = pathRetractStart
                     (assert_smaller (PathNext (PathNext pt14 stp42) stp23)
                                     (PathNext pt14 stp42))
                     (MkCmplxPath pt14 stp42)
  in (s5 ** PathNext pt52 stp23)

export
patRetractEnd : (pt13 : Path tr s1 s3) -> CmplxPath pt13 ->
                   (s2 ** Path tr s1 s2)
patRetractEnd (PathSingl _ _) (CmplxPath _) impossible
patRetractEnd (PathNext (PathSingl s1 stp12) stp23) _ =
  let (s2 ** Refl) = stepEnd stp12 in (s2 ** PathSingl s1 stp12)
patRetractEnd (PathNext (PathNext pt14 stp42) stp23) _ =
  let (s2 ** Refl) = stepEnd stp42 in (s2 ** PathNext pt14 stp42)
