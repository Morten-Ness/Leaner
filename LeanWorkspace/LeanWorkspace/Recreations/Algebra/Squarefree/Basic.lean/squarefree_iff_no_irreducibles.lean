import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [WfDvdMonoid R]

theorem squarefree_iff_no_irreducibles {x : R} (hx₀ : x ≠ 0) :
    Squarefree x ↔ ∀ p, Irreducible p → ¬ (p * p ∣ x) := by
  refine ⟨fun h p hp hp' ↦ hp.not_isUnit (h p hp'), fun h d hd ↦ by_contra fun hdu ↦ ?_⟩
  have hd₀ : d ≠ 0 := ne_zero_of_dvd_ne_zero (ne_zero_of_dvd_ne_zero hx₀ hd) (dvd_mul_left d d)
  obtain ⟨p, irr, dvd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd₀
  exact h p irr ((mul_dvd_mul dvd dvd).trans hd)

