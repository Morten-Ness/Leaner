import Mathlib

variable {R : Type*}

theorem star_prod [CommMonoid R] [StarMul R] {α : Type*} (s : Finset α) (f : α → R) :
    star (∏ x ∈ s, f x) = ∏ x ∈ s, star (f x) := map_prod (starMulAut : R ≃* R) _ _

