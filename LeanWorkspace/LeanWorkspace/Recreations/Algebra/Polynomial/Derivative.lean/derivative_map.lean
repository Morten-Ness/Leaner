import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_map [Semiring S] (p : R[X]) (f : R →+* S) :
    Polynomial.derivative (p.map f) = p.derivative.map f := by
  let n := max p.natDegree (map f p).natDegree
  rw [Polynomial.derivative_apply, Polynomial.derivative_apply]
  rw [sum_over_range' _ _ (n + 1) ((le_max_left _ _).trans_lt (lt_add_one _))]
  on_goal 1 => rw [sum_over_range' _ _ (n + 1) ((le_max_right _ _).trans_lt (lt_add_one _))]
  · simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, map_mul, coeff_map,
      map_natCast, Polynomial.map_natCast, Polynomial.map_pow, map_X]
  all_goals intro n; rw [zero_mul, C_0, zero_mul]

