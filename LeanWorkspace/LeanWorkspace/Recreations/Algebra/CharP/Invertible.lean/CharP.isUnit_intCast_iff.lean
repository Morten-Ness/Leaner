import Mathlib

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem CharP.isUnit_intCast_iff {z : ℤ} (hp : p.Prime) : IsUnit (z : R) ↔ ¬↑p ∣ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp [CharP.isUnit_natCast_iff hp, Int.ofNat_dvd]
  · simp [CharP.isUnit_natCast_iff hp, Int.dvd_neg, Int.ofNat_dvd]

