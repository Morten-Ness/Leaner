import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι → α} {g : ι → β} {s : Set ι}

theorem monovaryOn_iff_smul_rearrangement :
    MonovaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i • g j + f j • g i ≤ f i • g i + f j • g j := monovaryOn_iff_forall_smul_nonneg.trans <| forall₄_congr fun i _ j _ ↦ by
    simp [smul_sub, sub_smul, ← add_sub_right_comm, le_sub_iff_add_le, add_comm (f i • g i),
      add_comm (f i • g j)]

