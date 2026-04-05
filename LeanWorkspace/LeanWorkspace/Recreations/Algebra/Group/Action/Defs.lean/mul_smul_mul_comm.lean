import Mathlib

variable {M N G H α β γ δ : Type*}

theorem mul_smul_mul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] (a b : α) (c d : β) :
    (a * b) • (c * d) = (a • c) * (b • d) := smul_smul_smul_comm a b c d

