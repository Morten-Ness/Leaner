import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [Monoid S] [SMul R M] [SMul R S] [MulAction S M] [IsScalarTower R S M]

theorem of_smul_eq_one (h : a • s = 1) : IsSMulRegular M s := IsSMulRegular.of_smul a
    (by
      rw [h]
      exact IsSMulRegular.one M)

