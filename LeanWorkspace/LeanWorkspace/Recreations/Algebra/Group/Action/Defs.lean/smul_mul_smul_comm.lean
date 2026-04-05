import Mathlib

variable {M N G H α β γ δ : Type*}

theorem smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c : α) (d : β) :
    (a • b) * (c • d) = (a * c) • (b * d) := by
  have : SMulCommClass β α β := .symm ..; exact smul_smul_smul_comm a b c d

