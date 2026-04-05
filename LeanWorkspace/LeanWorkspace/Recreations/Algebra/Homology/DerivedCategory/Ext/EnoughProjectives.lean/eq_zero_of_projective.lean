import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
theorem eq_zero_of_projective [HasExt.{w} C] {P Y : C} {n : ℕ} [Projective P]
    (e : CategoryTheory.Abelian.Ext P Y (n + 1)) : e = 0 := by
  letI := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).hom.app _), zero_hom, Limits.zero_comp]
  apply DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
    (L := (CochainComplex.singleFunctor C (-(n + 1))).obj Y) (n := -(n + 1)) _ (by lia)

