import Mathlib

variable {ι κ β : Type*}

variable [CommMonoid β]

theorem prod_preimage (f : ι → κ) (s : Finset κ) (hf) (g : κ → β)
    (hg : ∀ x ∈ s, x ∉ Set.range f → g x = 1) :
    ∏ x ∈ s.preimage f hf, g (f x) = ∏ x ∈ s, g x := by
  classical rw [Finset.prod_preimage', prod_filter_of_ne]; exact fun x hx ↦ Not.imp_symm (hg x hx)

