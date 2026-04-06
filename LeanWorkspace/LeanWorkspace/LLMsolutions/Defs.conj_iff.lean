FAIL
import Mathlib

variable {S M G : Type*}

variable [Group G]

theorem conj_iff {a x y b : G} :
    SemiconjBy (b * a * b⁻¹) (b * x * b⁻¹) (b * y * b⁻¹) ↔ SemiconjBy a x y := by
  constructor
  · intro h
    exact ⟨by
      have h' := congrArg (fun t => b⁻¹ * t * b) h.1
      simpa [mul_assoc] using h'⟩
  · intro h
    exact ⟨by
      have h' := congrArg (fun t => b * t * b⁻¹) h.1
      simpa [mul_assoc] using h'⟩
