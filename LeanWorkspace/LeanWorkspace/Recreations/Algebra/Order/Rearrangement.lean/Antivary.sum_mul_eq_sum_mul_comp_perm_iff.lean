import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable {s : Finset ι} {σ : Perm ι} {f g : ι → α}

variable [Fintype ι]

theorem Antivary.sum_mul_eq_sum_mul_comp_perm_iff (hfg : Antivary f g) :
    ∑ i, f i * g (σ i) = ∑ i, f i * g i ↔ Antivary f (g ∘ σ) := hfg.sum_smul_comp_perm_eq_sum_smul_iff

