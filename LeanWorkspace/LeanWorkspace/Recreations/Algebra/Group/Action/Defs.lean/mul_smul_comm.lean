import Mathlib

variable {M N G H α β γ δ : Type*}

theorem mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s : α) (x y : β) :
    x * s • y = s • (x * y) := (smul_comm s x y).symm

