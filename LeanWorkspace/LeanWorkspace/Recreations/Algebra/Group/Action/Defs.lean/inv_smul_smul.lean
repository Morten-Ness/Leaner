import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

variable [Group G] [MulAction G α] {g : G} {a b : α}

theorem inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a := by rw [smul_smul, inv_mul_cancel, one_smul]

