import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι → α} {g : ι → β} {s : Set ι}

theorem antivaryOn_iff_smul_rearrangement :
    AntivaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i • g i + f j • g j ≤ f i • g j + f j • g i := monovaryOn_toDual_right.symm.trans <| by rw [monovaryOn_iff_smul_rearrangement]; rfl

