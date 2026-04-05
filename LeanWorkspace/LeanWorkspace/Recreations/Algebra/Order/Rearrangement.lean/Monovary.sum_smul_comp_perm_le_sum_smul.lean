import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

variable [Fintype ι]

theorem Monovary.sum_smul_comp_perm_le_sum_smul (hfg : Monovary f g) :
    ∑ i, f i • g (σ i) ≤ ∑ i, f i • g i := (hfg.monovaryOn _).sum_smul_comp_perm_le_sum_smul fun _ _ ↦ Finset.mem_univ _

