import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

variable [Group G] [MulAction G α] {g : G} {a b : α}

variable [Group H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H]

theorem smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹ := inv_eq_of_mul_eq_one_right <| by rw [smul_mul_smul_comm, mul_inv_cancel, mul_inv_cancel, one_smul]

