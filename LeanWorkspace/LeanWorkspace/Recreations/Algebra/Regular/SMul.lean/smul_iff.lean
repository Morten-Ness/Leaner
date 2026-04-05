import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [SMul R M] [SMul R S] [SMul S M] [IsScalarTower R S M]

theorem smul_iff (b : S) (ha : IsSMulRegular M a) : IsSMulRegular M (a • b) ↔ IsSMulRegular M b := ⟨IsSMulRegular.of_smul _, IsSMulRegular.smul ha⟩

