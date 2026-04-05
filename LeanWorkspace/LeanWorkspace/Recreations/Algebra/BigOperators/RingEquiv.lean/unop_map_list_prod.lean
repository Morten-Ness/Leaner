import Mathlib

variable {α R S : Type*}

theorem unop_map_list_prod [Semiring R] [Semiring S] (f : R ≃+* Sᵐᵒᵖ) (l : List R) :
    MulOpposite.unop (f l.prod) = (l.map (MulOpposite.unop ∘ f)).reverse.prod := unop_map_list_prod f l

