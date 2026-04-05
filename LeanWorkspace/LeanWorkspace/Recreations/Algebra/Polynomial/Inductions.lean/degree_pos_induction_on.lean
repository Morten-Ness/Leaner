import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem degree_pos_induction_on {P : R[X] → Prop} (p : R[X]) (h0 : 0 < degree p)
    (hC : ∀ {a}, a ≠ 0 → P (Polynomial.C a * Polynomial.X)) (hX : ∀ {p}, 0 < degree p → P p → P (p * Polynomial.X))
    (hadd : ∀ {p} {a}, 0 < degree p → P p → P (p + Polynomial.C a)) : P p := Polynomial.recOnHorner p (fun h => by rw [degree_zero] at h; exact absurd h (by decide))
    (fun p a heq0 _ ih h0 =>
      (have : 0 < degree p :=
        (lt_of_not_ge fun h =>
          not_lt_of_ge (degree_C_le (a := a)) <|
            by rwa [eq_C_of_degree_le_zero h, ← C_add, heq0, zero_add] at h0)
      hadd this (ih this)))
    (fun p _ ih h0' =>
      if h0 : 0 < degree p then hX h0 (ih h0)
      else by
        rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at h0' ⊢
        exact hC fun h : coeff p 0 = 0 => by simp [h] at h0')
    h0

