import Mathlib

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem CharP.isUnit_natCast_iff {n : ℕ} (hp : p.Prime) : IsUnit (n : R) ↔ ¬p ∣ n where
  mp h := by
    have := CharP.nontrivial_of_char_ne_one (R := R) hp.ne_one
    rw [← CharP.cast_eq_zero_iff (R := R)]
    exact h.ne_zero
  mpr not_dvd :=
    letI := invertibleOfCoprime (R := R) (hp.coprime_iff_not_dvd.2 not_dvd).symm
    isUnit_of_invertible _

