import Mathlib

variable {R : Type*}

theorem star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : Finset α) (f : α → R) :
    star (∑ x ∈ s, f x) = ∑ x ∈ s, star (f x) := map_sum (starAddEquiv : R ≃+ R) _ _

