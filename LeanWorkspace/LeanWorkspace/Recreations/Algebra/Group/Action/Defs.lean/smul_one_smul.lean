import Mathlib

variable {M N G H α β γ δ : Type*}

theorem smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α]
    [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y := by
  rw [smul_assoc, one_smul]

