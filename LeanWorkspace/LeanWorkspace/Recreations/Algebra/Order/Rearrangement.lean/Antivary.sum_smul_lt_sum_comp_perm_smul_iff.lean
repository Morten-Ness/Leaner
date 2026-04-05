import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulStrictMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

variable [Fintype ι]

theorem Antivary.sum_smul_lt_sum_comp_perm_smul_iff (hfg : Antivary f g) :
    ∑ i, f i • g i < ∑ i, f (σ i) • g i ↔ ¬Antivary (f ∘ σ) g := by
  simp [(hfg.antivaryOn _).sum_smul_lt_sum_comp_perm_smul_iff fun _ _ ↦ Finset.mem_univ _]

