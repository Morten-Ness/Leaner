import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [Monoid R] [MulAction R M]

theorem pow_iff {n : ℕ} (n0 : 0 < n) : IsSMulRegular M (a ^ n) ↔ IsSMulRegular M a := by
  refine ⟨?_, IsSMulRegular.pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0, pow_succ, ← smul_eq_mul]
  exact IsSMulRegular.of_smul _

