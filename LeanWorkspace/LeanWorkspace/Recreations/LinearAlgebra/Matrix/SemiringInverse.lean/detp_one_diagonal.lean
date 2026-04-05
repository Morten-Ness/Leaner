import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem detp_one_diagonal (d : n → R) : Matrix.detp 1 (diagonal d) = ∏ i, d i := by
  rw [Matrix.detp, sum_eq_single_of_mem 1]
  · simp
  · simp [ofSign]
  · rintro σ - hσ1
    obtain ⟨i, hi⟩ := not_forall.mp (mt Equiv.Perm.ext_iff.mpr hσ1)
    exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

