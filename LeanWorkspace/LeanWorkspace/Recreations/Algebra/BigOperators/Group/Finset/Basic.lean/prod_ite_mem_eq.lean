import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_ite_mem_eq [Fintype ι] (s : Finset ι) (f : ι → M) [DecidablePred (· ∈ s)] :
    (∏ i, if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  rw [← Finset.prod_filter]; congr; grind

