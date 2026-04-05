import Mathlib

variable {ι κ β : Type*}

variable [CommMonoid β]

theorem prod_preimage' (f : ι → κ) [DecidablePred (· ∈ Set.range f)] (s : Finset κ) (hf) (g : κ → β) :
    ∏ x ∈ s.preimage f hf, g (f x) = ∏ x ∈ s with x ∈ Set.range f, g x := by
  classical
  calc
    ∏ x ∈ preimage s f hf, g (f x) = ∏ x ∈ image f (preimage s f hf), g x :=
      Eq.symm <| prod_image <| by simpa [mem_preimage, Set.InjOn] using hf
    _ = ∏ x ∈ s with x ∈ Set.range f, g x := by rw [image_preimage]

