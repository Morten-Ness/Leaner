import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem ofAdd_image_zmultiples_eq_zpowers_ofAdd {x : A} :
    Multiplicative.ofAdd '' (AddSubgroup.zmultiples x : Set A) =
      Subgroup.zpowers (Multiplicative.ofAdd x) := by
  symm
  rw [Equiv.eq_image_iff_symm_image_eq]
  exact ofMul_image_zpowers_eq_zmultiples_ofMul

