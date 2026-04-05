import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem isAddUnit_detp_mul_detp {d : n → R} (hAB : A * B = diagonal d) :
    IsAddUnit (Matrix.detp 1 A * Matrix.detp (-1) B + Matrix.detp (-1) A * Matrix.detp 1 B) := by
  suffices h : ∀ {s t}, s ≠ t → IsAddUnit (Matrix.detp s A * Matrix.detp t B) from
    (h (by decide)).add (h (by decide))
  intro s t h
  simp_rw [Matrix.detp, sum_mul_sum, IsAddUnit.sum_iff]
  intro σ hσ τ hτ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ, ← hτ, ← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq, eq_comm, eq_inv_iff_mul_eq_one, eq_comm] at h
  simp_rw [Equiv.ext_iff, not_forall, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h
  obtain ⟨k, hk⟩ := h
  rw [mul_comm, ← Equiv.prod_comp σ, mul_comm, ← prod_mul_distrib,
    ← mul_prod_erase Finset.univ _ (mem_univ k), ← smul_eq_mul]
  exact (Matrix.isAddUnit_mul hAB k (τ (σ k)) (σ k) hk).smul_right _

