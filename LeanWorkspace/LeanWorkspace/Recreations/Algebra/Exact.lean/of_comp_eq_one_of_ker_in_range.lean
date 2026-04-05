import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem of_comp_eq_one_of_ker_in_range [One P] (hc : g.comp f = 1)
    (hr : ∀ y, g y = 1 → y ∈ Set.range f) :
    Function.MulExact f g := fun y ↦ ⟨hr y, fun ⟨x, hx⟩ ↦ hx ▸ congrFun hc x⟩

