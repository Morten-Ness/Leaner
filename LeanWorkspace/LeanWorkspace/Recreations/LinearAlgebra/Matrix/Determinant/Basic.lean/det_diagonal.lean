import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_diagonal {d : n → R} : Matrix.det (diagonal d) = ∏ i, d i := by
  rw [Matrix.det_apply']
  refine (Finset.sum_eq_single 1 ?_ ?_).trans ?_
  · rintro σ - h2
    obtain ⟨x, h3⟩ := not_forall.1 (mt Equiv.ext h2)
    convert mul_zero (ε σ)
    apply Finset.prod_eq_zero (mem_univ x)
    exact if_neg h3
  · simp
  · simp

