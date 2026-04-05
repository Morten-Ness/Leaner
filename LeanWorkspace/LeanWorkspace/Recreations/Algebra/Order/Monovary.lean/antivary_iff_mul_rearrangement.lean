import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι → α} {s : Set ι}

theorem antivary_iff_mul_rearrangement :
    Antivary f g ↔ ∀ i j, f i * g i + f j * g j ≤ f i * g j + f j * g i := by
  simp only [smul_eq_mul, antivary_iff_smul_rearrangement]

alias ⟨MonovaryOn.sub_mul_sub_nonneg, _⟩ := monovaryOn_iff_forall_mul_nonneg
alias ⟨AntivaryOn.sub_mul_sub_nonpos, _⟩ := antivaryOn_iff_forall_mul_nonpos
alias ⟨Monovary.sub_mul_sub_nonneg, _⟩ := monovary_iff_forall_mul_nonneg
alias ⟨Antivary.sub_mul_sub_nonpos, _⟩ := antivary_iff_forall_mul_nonpos
alias ⟨Monovary.mul_add_mul_le_mul_add_mul, _⟩ := monovary_iff_mul_rearrangement
alias ⟨Antivary.mul_add_mul_le_mul_add_mul, _⟩ := antivary_iff_mul_rearrangement
alias ⟨MonovaryOn.mul_add_mul_le_mul_add_mul, _⟩ := monovaryOn_iff_mul_rearrangement
alias ⟨AntivaryOn.mul_add_mul_le_mul_add_mul, _⟩ := antivaryOn_iff_mul_rearrangement

