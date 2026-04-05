import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem bot_prod_bot : (⊥ : Subsemigroup M).prod (⊥ : Subsemigroup N) = ⊥ := SetLike.coe_injective <| by simp [Subsemigroup.coe_prod]

