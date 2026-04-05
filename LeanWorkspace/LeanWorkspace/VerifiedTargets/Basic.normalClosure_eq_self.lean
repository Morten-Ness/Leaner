import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_eq_self (H : Subgroup G) [H.Normal] : Subgroup.normalClosure ↑H = H := le_antisymm (Subgroup.normalClosure_le_normal rfl.subset) Subgroup.le_normalClosure

