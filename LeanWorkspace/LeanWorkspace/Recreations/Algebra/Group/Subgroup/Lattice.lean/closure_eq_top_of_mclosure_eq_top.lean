import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_eq_top_of_mclosure_eq_top {S : Set G} (h : Submonoid.closure S = ⊤) :
    Subgroup.closure S = ⊤ := (Subgroup.eq_top_iff' _).2 fun _ => Subgroup.le_closure_toSubmonoid _ <| h.symm ▸ trivial

