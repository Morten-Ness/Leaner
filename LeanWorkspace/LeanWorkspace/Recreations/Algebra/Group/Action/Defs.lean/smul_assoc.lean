import Mathlib

variable {M N G H α β γ δ : Type*}

theorem smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α] (x : M) (y : N)
    (z : α) : (x • y) • z = x • y • z := IsScalarTower.smul_assoc x y z

