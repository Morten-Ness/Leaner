import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

variable [Group G] [MulAction G α] {g : G} {a b : α}

variable [Group H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H]

theorem smul_zpow (g : G) (a : H) (n : ℤ) : (g • a) ^ n = g ^ n • a ^ n := by
  cases n <;> simp [smul_pow, smul_inv]

