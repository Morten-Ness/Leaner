import Mathlib

theorem eq_on_inv {F G M} [Group G] [Monoid M] [FunLike F G M] [MonoidHomClass F G M]
    (f g : F) {x : G} (h : f x = g x) : f x⁻¹ = g x⁻¹ := (Group.isUnit x).eq_on_inv f g h

