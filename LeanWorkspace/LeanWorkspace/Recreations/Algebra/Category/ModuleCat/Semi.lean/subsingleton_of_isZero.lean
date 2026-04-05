import Mathlib

variable (R : Type u) [Semiring R]

variable {X₁ X₂ : Type v}

variable {M N : SemimoduleCat.{v} R}

theorem subsingleton_of_isZero (h : IsZero M) : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 (fun x ↦ ?_)
  rw [← LinearMap.id_apply (R := R) x, ← SemimoduleCat.hom_id]
  simp only [(CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp h, hom_zero, LinearMap.zero_apply]

