import Mathlib

section

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem CharP.intCast_mul_natCast_gcdA_eq_gcd (n : ℕ) :
    (n * n.gcdA p : R) = n.gcd p := by
  suffices ↑(n * n.gcdA p + p * n.gcdB p : ℤ) = ((n.gcd p : ℤ) : R) by simpa using this
  rw [← Nat.gcd_eq_gcd_ab]

end

section

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem CharP.isUnit_intCast_iff {z : ℤ} (hp : p.Prime) : IsUnit (z : R) ↔ ¬↑p ∣ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp [CharP.isUnit_natCast_iff hp, Int.ofNat_dvd]
  · simp [CharP.isUnit_natCast_iff hp, Int.dvd_neg, Int.ofNat_dvd]

end

section

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

end

section

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem CharP.natCast_gcdA_mul_intCast_eq_gcd (n : ℕ) :
    (n.gcdA p * n : R) = n.gcd p := Nat.commute_cast _ _ |>.eq.trans <| CharP.intCast_mul_natCast_gcdA_eq_gcd n

end

section

variable {R K : Type*}

theorem Even.all [Semiring R] [Invertible (2 : R)] (a : R) : Even a := .of_isUnit_two (isUnit_of_invertible _) _

end

section

variable {R K : Type*}

theorem Odd.all [Ring R] [Invertible (2 : R)] (a : R) : Odd a := .of_isUnit_two (isUnit_of_invertible _) _

end

section

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem invOf_eq_of_coprime {n : ℕ} [Invertible (n : R)] (h : n.Coprime p) :
    ⅟(n : R) = n.gcdA p := by
  letI : Invertible (n : R) := invertibleOfCoprime h
  convert (rfl : ⅟(n : R) = _)

end

section

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem not_ringChar_dvd_of_invertible {t : ℕ} [Invertible (t : R)] [Nontrivial R] :
    ¬ringChar R ∣ t := by
  rw [← ringChar.spec, ← Ne]
  exact Invertible.ne_zero (t : R)

end
