import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable {s : Finset ι} {σ : Perm ι} {f g : ι → α}

variable [Fintype ι]

theorem Antivary.sum_mul_le_sum_comp_perm_mul (hfg : Antivary f g) :
    ∑ i, f i * g i ≤ ∑ i, f (σ i) * g i := hfg.sum_smul_le_sum_comp_perm_smul

