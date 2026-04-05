import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [Monoid R] [MulAction R M]

theorem pow (n : ℕ) (ra : IsSMulRegular M a) : IsSMulRegular M (a ^ n) := by
  induction n with
  | zero => rw [pow_zero]; simp only [IsSMulRegular.one]
  | succ n hn =>
    rw [pow_succ']
    exact (IsSMulRegular.smul_iff ra (a ^ n)).mpr hn

