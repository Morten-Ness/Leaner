import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

variable [Group G] [MulAction G α] {g : G} {a b : α}

theorem smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a := by rw [smul_smul, mul_inv_cancel, one_smul]

