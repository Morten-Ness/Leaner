import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_comp_eq_of_range_subset {g : M → N} {f : ι → M}
    (hg : ∀ {x}, x ∈ Set.range f → (g x = 1 ↔ x = 1)) :
    Function.mulSupport (g ∘ f) = Function.mulSupport f := Set.ext fun x ↦ not_congr <| by rw [Function.comp, hg (mem_range_self x)]

