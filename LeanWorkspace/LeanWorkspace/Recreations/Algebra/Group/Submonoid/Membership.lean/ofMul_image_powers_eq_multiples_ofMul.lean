import Mathlib

variable {M A B : Type*}

theorem ofMul_image_powers_eq_multiples_ofMul [Monoid M] {x : M} :
    Additive.ofMul '' (Submonoid.powers x : Set M) = AddSubmonoid.multiples (Additive.ofMul x) := by
  ext
  exact Set.mem_image_iff_of_inverse (congrFun rfl) (congrFun rfl)

