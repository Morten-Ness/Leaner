import Mathlib

variable {M N G H α β γ δ : Type*}

variable [SMul M α]

theorem Commute.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute a (r • b) := (mul_smul_comm _ _ _).trans ((congr_arg _ h).trans <| (smul_mul_assoc _ _ _).symm)

