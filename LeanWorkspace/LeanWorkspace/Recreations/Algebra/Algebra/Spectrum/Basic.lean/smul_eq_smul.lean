import Mathlib

open scoped Pointwise Ring

variable {𝕜 : Type u} {A : Type v}

variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem smul_eq_smul [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty) :
    σ (k • a) = k • σ a := by
  rcases eq_or_ne k 0 with (rfl | h)
  · simpa [ha, zero_smul_set] using (show {(0 : 𝕜)} = (0 : Set 𝕜) from rfl)
  · exact spectrum.unit_smul_eq_smul a (Units.mk0 k h)

