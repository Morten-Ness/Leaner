import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable {s : Finset ι} {σ : Perm ι} {f g : ι → α}

variable [Fintype ι]

theorem Monovary.sum_mul_comp_perm_le_sum_mul (hfg : Monovary f g) :
    ∑ i, f i * g (σ i) ≤ ∑ i, f i * g i := hfg.sum_smul_comp_perm_le_sum_smul

