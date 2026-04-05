import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem detp_neg_one_diagonal (d : n → R) : Matrix.detp (-1) (diagonal d) = 0 := by
  rw [Matrix.detp, sum_eq_zero]
  intro σ hσ
  have hσ1 : σ ≠ 1 := by
    contrapose! hσ
    rw [hσ, mem_ofSign, sign_one]
    decide
  obtain ⟨i, hi⟩ := not_forall.mp (mt Equiv.Perm.ext_iff.mpr hσ1)
  exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

