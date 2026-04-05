import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (g : S →+* T) (f : R →+* S)

theorem rangeS_eq_top : f.rangeS = ⊤ ↔ Function.Surjective f := by
  simp [← Set.range_eq_univ, SetLike.ext'_iff]

