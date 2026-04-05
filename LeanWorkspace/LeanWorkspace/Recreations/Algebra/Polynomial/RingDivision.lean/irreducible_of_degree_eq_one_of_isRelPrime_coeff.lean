import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem irreducible_of_degree_eq_one_of_isRelPrime_coeff
    {p : R[X]} (hp : p.degree = 1) (hc : IsRelPrime (p.coeff 0) (p.coeff 1)) :
    Irreducible p where
  not_isUnit h := by
    obtain ⟨u, -, h⟩ := isUnit_iff.mp h
    apply not_le.mpr (zero_lt_one' (WithBot ℕ))
    simp [← hp, ← h, degree_C_le]
  isUnit_or_isUnit f g h := by
    wlog! H : f.degree ≤ g.degree generalizing f g
    · rw [mul_comm] at h
      exact (this g f h H.le).symm
    left
    rw [h, degree_mul, Nat.WithBot.add_eq_one_iff] at hp
    rcases hp with ⟨hf, hg⟩ | ⟨hf, hg⟩; swap
    · simp [← not_lt, hf, hg] at H
    replace hf := f.eq_C_of_degree_eq_zero hf
    rw [hf]
    apply IsUnit.map Polynomial.C
    rw [h, hf, coeff_C_mul, coeff_C_mul] at hc
    apply hc <;> simp

