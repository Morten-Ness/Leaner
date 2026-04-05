import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem _root_.Subgroup.ker_subtype (H : Subgroup G) : H.subtype.ker = ⊥ := H.MonoidHom.ker_eq_bot_iff subtype.mpr Subtype.coe_injective

