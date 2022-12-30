---------------------
-- Module declaration
---------------------

module Stm.Data.Path.CmplxPath

-------------------
-- External imports
-------------------

import Decidable.Decidable

-------------------
-- Internal imports
-------------------

import Stm.Data.Path.Path
import Stm.Data.Step.Step
import Stm.Data.Stm.Stm

--------------------------
-- Complex path definition
--------------------------

public export
data CmplxPath : Path tr s1 s3 -> Type where
  MkCmplxPath : (pt12 : Path tr s1 s2) -> (stp23 : Step tr s2 s3) ->
                CmplxPath (PathNext pt12 stp23)

export
decCmplxPath : (pt : Path tr s1 s2) -> Dec (CmplxPath pt)
decCmplxPath (PathSingl _ _) = No (\prf => case prf of _ impossible)
decCmplxPath (PathNext pt12 stp23) = Yes (MkCmplxPath pt12 stp23)
