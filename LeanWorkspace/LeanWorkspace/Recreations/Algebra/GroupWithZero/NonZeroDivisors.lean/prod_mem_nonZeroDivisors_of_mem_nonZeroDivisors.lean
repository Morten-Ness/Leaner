import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors
    {ι : Type*} {s : Finset ι} {f : ι → M₀} (h : ∀ i ∈ s, f i ∈ M₀⁰) :
    ∏ i ∈ s, f i ∈ M₀⁰ := s.prod_induction _ _ (fun _ _ ↦ and_imp.mp mul_mem_nonZeroDivisors.mpr) (one_mem _) h

