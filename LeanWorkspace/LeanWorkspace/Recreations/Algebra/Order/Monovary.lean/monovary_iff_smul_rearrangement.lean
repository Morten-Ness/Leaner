import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι → α} {g : ι → β} {s : Set ι}

theorem monovary_iff_smul_rearrangement :
    Monovary f g ↔ ∀ i j, f i • g j + f j • g i ≤ f i • g i + f j • g j := monovaryOn_univ.symm.trans <| monovaryOn_iff_smul_rearrangement.trans <| by
    simp only [Set.mem_univ, forall_true_left]

