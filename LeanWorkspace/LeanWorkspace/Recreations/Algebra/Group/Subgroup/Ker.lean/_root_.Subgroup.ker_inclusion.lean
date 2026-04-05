import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem _root_.Subgroup.ker_inclusion {H K : Subgroup G} (h : H ≤ K) : (inclusion h).ker = ⊥ := MonoidHom.ker_eq_bot_iff (inclusion h).mpr (Set.inclusion_injective h)

