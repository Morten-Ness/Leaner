import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem of_comp_of_mem_range [One P] (h1 : g ∘ f = 1)
    (h2 : ∀ x, g x = 1 → x ∈ Set.range f) : Function.MulExact f g := fun y => Iff.intro (h2 y) <|
    Exists.rec ((forall_apply_eq_imp_iff (p := (g · = 1))).mpr (congrFun h1) y)

