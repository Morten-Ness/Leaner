import Mathlib

variable {M A B : Type*}

theorem ofAdd_image_multiples_eq_powers_ofAdd [AddMonoid A] {x : A} :
    Multiplicative.ofAdd '' (AddSubmonoid.multiples x : Set A) =
      Submonoid.powers (Multiplicative.ofAdd x) := by
  symm
  rw [Equiv.eq_image_iff_symm_image_eq]
  exact ofMul_image_powers_eq_multiples_ofMul

