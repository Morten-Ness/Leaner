import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable {s : Finset ι} {σ : Perm ι} {f g : ι → α}

variable [Fintype ι]

theorem Antivary.sum_mul_le_sum_mul_comp_perm (hfg : Antivary f g) :
    ∑ i, f i * g i ≤ ∑ i, f i * g (σ i) := hfg.sum_smul_le_sum_smul_comp_perm

