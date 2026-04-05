import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

theorem preadditiveYoneda_homologySequenceδ_singleTriangle_apply
    [HasDerivedCategory.{w'} C] {Y : C} {n₀ : ℕ} (x : CategoryTheory.Abelian.Ext S.X₁ Y n₀)
    {n₁ : ℕ} (h : 1 + n₀ = n₁) :
    (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequenceδ
      ((triangleOpEquivalence _).functor.obj (op hS.singleTriangle)) n₀ n₁ (by lia) x.hom =
      (hS.extClass.comp x h).hom := by
  rw [preadditiveYoneda_homologySequenceδ_apply,
    comp_hom, hS.extClass_hom, ShiftedHom.comp]
  rfl

