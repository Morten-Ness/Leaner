import Mathlib

variable {R S M M₂ : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

theorem Int.cast_smul_eq_zsmul (n : ℤ) (b : M) : (n : R) • b = n • b := by
  cases n with
  | ofNat => simp [Nat.cast_smul_eq_nsmul]
  | negSucc => simp [add_smul, Nat.cast_smul_eq_nsmul]

