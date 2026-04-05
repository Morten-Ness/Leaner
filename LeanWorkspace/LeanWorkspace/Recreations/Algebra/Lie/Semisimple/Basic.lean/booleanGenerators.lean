import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

variable [IsSemisimple R L]

theorem booleanGenerators : BooleanGenerators {I : LieIdeal R L | IsAtom I} where
  isAtom _ hI := hI
  LieAlgebra.IsSemisimple.finitelyAtomistic _ _ hs _ hIs := LieAlgebra.IsSemisimple.finitelyAtomistic _ hs _ hIs

