import Mathlib

open scoped Function -- required for scoped `on` notation Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem natDegree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : ∀ x : R, f x = 0 → x = 0) : 0 < natDegree p := lt_of_not_ge fun hlt => by
    have A : p = Polynomial.C (p.coeff 0) := eq_C_of_natDegree_le_zero hlt
    rw [A, eval₂_C] at hz
    simp only [inj (p.coeff 0) hz, map_zero] at A
    exact hp A

