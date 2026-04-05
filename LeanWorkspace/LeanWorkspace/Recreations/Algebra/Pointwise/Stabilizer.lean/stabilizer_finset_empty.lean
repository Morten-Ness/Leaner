import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

variable [DecidableEq α]

theorem stabilizer_finset_empty : stabilizer G (∅ : Finset α) = ⊤ := Subgroup.coe_eq_univ.1 <| eq_univ_of_forall Finset.smul_finset_empty

