import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

theorem ext_iff (A B : Matrix.SpecialLinearGroup n R) : A = B ↔ ∀ i j, A i j = B i j := Subtype.ext_iff.trans Matrix.ext_iff.symm

