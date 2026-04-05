import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_closure_eq_normalClosure {s : Set G} :
    Subgroup.normalClosure ↑(closure s) = Subgroup.normalClosure s := le_antisymm (Subgroup.normalClosure_le_normal Subgroup.closure_le_normalClosure) (Subgroup.normalClosure_mono subset_closure)

