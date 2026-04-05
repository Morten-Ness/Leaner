import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι → α} {g : ι → β} {s : Set ι}

theorem antivaryOn_iff_forall_smul_nonpos :
    AntivaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f j - f i) • (g j - g i) ≤ 0 := monovaryOn_toDual_right.symm.trans <| by rw [monovaryOn_iff_forall_smul_nonneg]; rfl

