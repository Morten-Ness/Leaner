import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem Monic.eq_one_of_isUnit (hm : Polynomial.Monic p) (hpu : IsUnit p) : p = 1 := by
  nontriviality R
  obtain ⟨q, h⟩ := hpu.exists_right_inv
  have := hm.natDegree_mul' (right_ne_zero_of_mul_eq_one h)
  rw [h, natDegree_one, eq_comm, add_eq_zero] at this
  exact hm.natDegree_eq_zero.mp this.1

