import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

variable (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)

theorem contravariant_sequence_exact₁' :
    (ShortComplex.mk (AddCommGrpCat.ofHom (((mk₀ S.f).precomp Y (zero_add n₀))))
      (AddCommGrpCat.ofHom (hS.extClass.precomp Y h)) (by
        ext
        dsimp
        simp only [ShortComplex.ShortExact.extClass_comp_assoc])).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₃ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by lia)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := CategoryTheory.Abelian.Ext.homAddEquiv)
    (e₂ := CategoryTheory.Abelian.Ext.homAddEquiv) (e₃ := CategoryTheory.Abelian.Ext.homAddEquiv) (H := this)
  · ext; apply CategoryTheory.Abelian.Ext.singleFunctor_map_comp_hom (C := C)
  · ext; dsimp; apply CategoryTheory.Abelian.Ext.preadditiveYoneda_homologySequenceδ_singleTriangle_apply

