import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

variable (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

theorem covariant_sequence_exact₁' :
    (ShortComplex.mk
      (AddCommGrpCat.ofHom (hS.extClass.postcomp X h))
      (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₁))) (by
        ext x
        dsimp
        simp only [comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp,
          comp_zero])).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₁ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := CategoryTheory.Abelian.Ext.homAddEquiv)
    (e₂ := CategoryTheory.Abelian.Ext.homAddEquiv) (e₃ := CategoryTheory.Abelian.Ext.homAddEquiv) (H := this)
  · ext x
    exact CategoryTheory.Abelian.Ext.preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h
  · ext x; apply CategoryTheory.Abelian.Ext.hom_comp_singleFunctor_map_shift (C := C)

