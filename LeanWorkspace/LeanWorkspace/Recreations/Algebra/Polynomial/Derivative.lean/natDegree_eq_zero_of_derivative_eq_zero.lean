import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem natDegree_eq_zero_of_derivative_eq_zero [IsAddTorsionFree R] {f : R[X]}
    (h : Polynomial.derivative f = 0) : f.natDegree = 0 := by
  rcases eq_or_ne f 0 with (rfl | hf)
  · exact natDegree_zero
  rw [natDegree_eq_zero_iff_degree_le_zero]
  by_contra! f_nat_degree_pos
  rw [← natDegree_pos_iff_degree_pos] at f_nat_degree_pos
  let m := f.natDegree - 1
  have hm : m + 1 = f.natDegree := tsub_add_cancel_of_le f_nat_degree_pos
  have h2 := Polynomial.coeff_derivative f m
  rw [Polynomial.ext_iff] at h
  rw [h m, coeff_zero, ← Nat.cast_add_one, ← nsmul_eq_mul', eq_comm, smul_eq_zero] at h2
  replace h2 := h2.resolve_left m.succ_ne_zero
  rw [hm, ← leadingCoeff, leadingCoeff_eq_zero] at h2
  exact hf h2

