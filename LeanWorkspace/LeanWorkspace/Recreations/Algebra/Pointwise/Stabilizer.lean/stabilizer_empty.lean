import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

theorem stabilizer_empty : stabilizer G (∅ : Set α) = ⊤ := Subgroup.coe_eq_univ.1 <| eq_univ_of_forall fun _a ↦ smul_set_empty

