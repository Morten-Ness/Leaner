import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_eq_iInf :
    Subgroup.normalClosure s = ⨅ (N : Subgroup G) (_ : Normal N) (_ : s ⊆ N), N := le_antisymm (le_iInf fun _ => le_iInf fun _ => le_iInf Subgroup.normalClosure_le_normal)
    (iInf_le_of_le (Subgroup.normalClosure s)
      (iInf_le_of_le (by infer_instance) (iInf_le_of_le Subgroup.subset_normalClosure le_rfl)))

