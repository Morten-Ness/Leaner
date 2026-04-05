import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_zsmul [AddGroup R] [StarAddMonoid R] (n : ℤ) (x : R) : star (n • x) = n • star x := (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _

