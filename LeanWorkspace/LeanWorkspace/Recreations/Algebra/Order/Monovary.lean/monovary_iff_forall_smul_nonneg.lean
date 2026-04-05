import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι → α} {g : ι → β} {s : Set ι}

theorem monovary_iff_forall_smul_nonneg : Monovary f g ↔ ∀ i j, 0 ≤ (f j - f i) • (g j - g i) := monovaryOn_univ.symm.trans <| monovaryOn_iff_forall_smul_nonneg.trans <| by
    simp only [Set.mem_univ, forall_true_left]

