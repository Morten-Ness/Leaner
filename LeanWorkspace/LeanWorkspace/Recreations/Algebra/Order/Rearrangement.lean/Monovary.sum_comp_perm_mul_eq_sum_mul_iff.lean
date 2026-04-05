import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable {s : Finset ι} {σ : Perm ι} {f g : ι → α}

variable [Fintype ι]

theorem Monovary.sum_comp_perm_mul_eq_sum_mul_iff (hfg : Monovary f g) :
    ∑ i, f (σ i) * g i = ∑ i, f i * g i ↔ Monovary (f ∘ σ) g := hfg.sum_comp_perm_smul_eq_sum_smul_iff

