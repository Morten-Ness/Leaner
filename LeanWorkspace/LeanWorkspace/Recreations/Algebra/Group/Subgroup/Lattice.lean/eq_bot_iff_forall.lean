import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem eq_bot_iff_forall : H = ⊥ ↔ ∀ x ∈ H, x = (1 : G) := toSubmonoid_injective.eq_iff.symm.trans <| Submonoid.eq_bot_iff_forall _

