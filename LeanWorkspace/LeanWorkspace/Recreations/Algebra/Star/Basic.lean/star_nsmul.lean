import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_nsmul [AddMonoid R] [StarAddMonoid R] (n : ℕ) (x : R) : star (n • x) = n • star x := (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _

