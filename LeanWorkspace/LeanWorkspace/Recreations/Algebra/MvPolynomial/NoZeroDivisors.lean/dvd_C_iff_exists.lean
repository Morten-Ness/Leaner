import Mathlib

variable {R : Type*}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R]

variable {p q : MvPolynomial σ R}

variable [NoZeroDivisors R]

theorem dvd_C_iff_exists {f : MvPolynomial σ R} {a : R} (ha : a ≠ 0) :
    f ∣ C a ↔ ∃ b, b ∣ a ∧ f = C b := by
  constructor
  · intro hf
    use coeff 0 f
    suffices f.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      refine ⟨?_, this⟩
      rw [this, C_dvd_iff_dvd_coeff] at hf
      simpa using hf 0
    apply Nat.eq_zero_of_le_zero
    simpa using MvPolynomial.totalDegree_le_of_dvd_of_isDomain hf (by simp [ha])
  · rintro ⟨b, hab, rfl⟩
    exact map_dvd C hab

