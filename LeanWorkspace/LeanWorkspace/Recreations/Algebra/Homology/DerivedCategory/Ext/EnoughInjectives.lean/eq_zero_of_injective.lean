import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
theorem eq_zero_of_injective [HasExt.{w} C] {X I : C} {n : ℕ} [Function.Injective I]
    (e : CategoryTheory.Abelian.Ext X I (n + 1)) : e = 0 := by
  let K := (CochainComplex.singleFunctor C 0).obj X
  have := K.isStrictlyGE_of_ge (-n) 0 (by lia)
  letI := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).hom.app _), zero_hom, Limits.zero_comp]
  exact DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective (K := K) (n := -n) _ (by lia)

