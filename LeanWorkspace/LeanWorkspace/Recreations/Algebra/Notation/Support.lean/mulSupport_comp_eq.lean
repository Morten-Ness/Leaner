import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_comp_eq (g : M → N) (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : ι → M) :
    Function.mulSupport (g ∘ f) = Function.mulSupport f := Set.ext fun _ ↦ not_congr hg

