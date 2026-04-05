import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [SMul R M] [SMul R S] [SMul S M] [IsScalarTower R S M]

theorem smul (ra : IsSMulRegular M a) (rs : IsSMulRegular M s) : IsSMulRegular M (a • s) := fun _ _ ab => rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))

