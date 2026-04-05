import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable {s : Finset ι} {σ : Perm ι} {f g : ι → α}

variable [Fintype ι]

theorem Monovary.sum_comp_perm_mul_le_sum_mul (hfg : Monovary f g) :
    ∑ i, f (σ i) * g i ≤ ∑ i, f i * g i := hfg.sum_comp_perm_smul_le_sum_smul

