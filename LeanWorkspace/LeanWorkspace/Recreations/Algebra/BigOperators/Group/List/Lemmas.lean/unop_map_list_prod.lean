import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N]

theorem unop_map_list_prod {F : Type*} [FunLike F M Nᵐᵒᵖ] [MonoidHomClass F M Nᵐᵒᵖ]
    (f : F) (l : List M) :
    (f l.prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.prod := by
  rw [map_list_prod f l, MulOpposite.unop_list_prod, List.map_map]

