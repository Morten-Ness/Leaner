import Mathlib

variable {M N G H α β γ δ : Type*}

theorem smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x * y = r • (x * y) := smul_assoc r x y

