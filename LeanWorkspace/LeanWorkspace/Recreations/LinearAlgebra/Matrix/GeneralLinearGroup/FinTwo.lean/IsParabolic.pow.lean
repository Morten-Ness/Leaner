import Mathlib

variable {R K : Type*} [CommRing R] [Field K]

theorem IsParabolic.pow {g : GL (Fin 2) K} (hg : Matrix.IsParabolic g) [CharZero K]
    {n : ℕ} (hn : n ≠ 0) : Matrix.IsParabolic (g ^ n) := by
  rw [Matrix.IsParabolic, Matrix.isParabolic_iff_exists] at hg ⊢
  obtain ⟨a, m, hg, hm0, hmsq⟩ := hg
  refine ⟨a ^ n, (n * a ^ (n - 1)) • m, ?_, ?_, by simp [smul_pow, hmsq]⟩
  · rw [Units.val_pow_eq_pow_val, hg]
    rw [← Nat.one_le_iff_ne_zero] at hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn IH =>
      simp only [pow_succ, IH, add_mul, Nat.add_sub_cancel, mul_add, ← map_mul, add_assoc]
      simp only [scalar_apply, ← smul_eq_mul_diagonal, ← SemigroupAction.mul_smul,
        ← smul_eq_diagonal_mul, smul_mul, ← sq, hmsq, smul_zero, add_zero, ← add_smul,
        Nat.cast_add_one, add_mul, one_mul]
      rw [(by lia : n = n - 1 + 1), pow_succ, (by lia : n - 1 + 1 = n)]
      ring_nf
  · suffices a ≠ 0 by simp [this, hm0, hn]
    refine fun ha ↦ (g ^ 2).det_ne_zero ?_
    rw [ha, map_zero, zero_add] at hg
    rw [← hg] at hmsq
    rw [Units.val_pow_eq_pow_val, hmsq, det_zero ⟨0⟩]

