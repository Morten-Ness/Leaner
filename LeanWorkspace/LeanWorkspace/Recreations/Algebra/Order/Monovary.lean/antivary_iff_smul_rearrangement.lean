import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι → α} {g : ι → β} {s : Set ι}

theorem antivary_iff_smul_rearrangement :
    Antivary f g ↔ ∀ i j, f i • g i + f j • g j ≤ f i • g j + f j • g i := monovary_toDual_right.symm.trans <| by rw [monovary_iff_smul_rearrangement]; rfl

alias ⟨MonovaryOn.sub_smul_sub_nonneg, _⟩ := monovaryOn_iff_forall_smul_nonneg
alias ⟨AntivaryOn.sub_smul_sub_nonpos, _⟩ := antivaryOn_iff_forall_smul_nonpos
alias ⟨Monovary.sub_smul_sub_nonneg, _⟩ := monovary_iff_forall_smul_nonneg
alias ⟨Antivary.sub_smul_sub_nonpos, _⟩ := antivary_iff_forall_smul_nonpos
alias ⟨Monovary.smul_add_smul_le_smul_add_smul, _⟩ := monovary_iff_smul_rearrangement
alias ⟨Antivary.smul_add_smul_le_smul_add_smul, _⟩ := antivary_iff_smul_rearrangement
alias ⟨MonovaryOn.smul_add_smul_le_smul_add_smul, _⟩ := monovaryOn_iff_smul_rearrangement
alias ⟨AntivaryOn.smul_add_smul_le_smul_add_smul, _⟩ := antivaryOn_iff_smul_rearrangement

