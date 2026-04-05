import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_top (K : Subgroup G) : K.prod (⊤ : Subgroup N) = K.comap (MonoidHom.fst G N) := ext fun x => by simp [Subgroup.mem_prod, MonoidHom.coe_fst]

