import Mathlib

theorem IsUnit.eq_on_inv {F G N} [DivisionMonoid G] [Monoid N] [FunLike F G N]
    [MonoidHomClass F G N] {x : G} (hx : IsUnit x) (f g : F) (h : f x = g x) : f x⁻¹ = g x⁻¹ := left_inv_eq_right_inv (map_mul_eq_one f hx.inv_mul_cancel)
    (h.symm ▸ map_mul_eq_one g (hx.mul_inv_cancel))

