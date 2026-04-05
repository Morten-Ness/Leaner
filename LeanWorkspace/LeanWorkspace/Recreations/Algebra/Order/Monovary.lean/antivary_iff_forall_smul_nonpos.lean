import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι → α} {g : ι → β} {s : Set ι}

theorem antivary_iff_forall_smul_nonpos : Antivary f g ↔ ∀ i j, (f j - f i) • (g j - g i) ≤ 0 := monovary_toDual_right.symm.trans <| by rw [monovary_iff_forall_smul_nonneg]; rfl

