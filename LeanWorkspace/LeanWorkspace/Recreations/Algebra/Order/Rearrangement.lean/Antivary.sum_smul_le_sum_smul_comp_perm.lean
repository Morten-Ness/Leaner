import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

variable [Fintype ι]

theorem Antivary.sum_smul_le_sum_smul_comp_perm (hfg : Antivary f g) :
    ∑ i, f i • g i ≤ ∑ i, f i • g (σ i) := (hfg.antivaryOn _).sum_smul_le_sum_smul_comp_perm fun _ _ ↦ Finset.mem_univ _

