import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (g : S →+* T) (f : R →+* S)

theorem rangeS_eq_map (f : R →+* S) : f.rangeS = (⊤ : Subsemiring R).map f := by
  ext
  simp

