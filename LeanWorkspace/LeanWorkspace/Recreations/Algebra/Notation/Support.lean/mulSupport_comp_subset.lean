import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_comp_subset {g : M → N} (hg : g 1 = 1) (f : ι → M) :
    Function.mulSupport (g ∘ f) ⊆ Function.mulSupport f := fun x ↦ mt fun h ↦ by simp only [(· ∘ ·), *]

