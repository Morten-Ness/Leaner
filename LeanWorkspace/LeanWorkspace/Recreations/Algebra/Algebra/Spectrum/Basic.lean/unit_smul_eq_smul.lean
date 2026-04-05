import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem unit_smul_eq_smul (a : A) (r : Rˣ) : σ (r • a) = r • σ a := by
  ext x
  have x_eq : x = r • r⁻¹ • x := by simp
  nth_rw 1 [x_eq]
  rw [spectrum.smul_mem_smul_iff]
  constructor
  · exact fun h => ⟨r⁻¹ • x, ⟨h, show r • r⁻¹ • x = x by simp⟩⟩
  · rintro ⟨w, _, (x'_eq : r • w = x)⟩
    simpa [← x'_eq]

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : Rˣ`

