import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable {s : Finset ι} {σ : Perm ι} {f g : ι → α}

variable [Fintype ι]

theorem Antivary.sum_mul_lt_sum_comp_perm_mul_iff (hfg : Antivary f g) :
    ∑ i, f i * g i < ∑ i, f (σ i) * g i ↔ ¬Antivary (f ∘ σ) g := hfg.sum_smul_lt_sum_comp_perm_smul_iff

