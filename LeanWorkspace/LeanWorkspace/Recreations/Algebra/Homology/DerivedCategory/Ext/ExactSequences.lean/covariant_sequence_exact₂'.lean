import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

include hS in
theorem covariant_sequence_exact₂' (n : ℕ) :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n)))
      (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n))) (by
        ext x
        dsimp
        simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, ShortComplex.zero, mk₀_zero,
          comp_zero])).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₂ _
    (hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := CategoryTheory.Abelian.Ext.homAddEquiv)
    (e₂ := CategoryTheory.Abelian.Ext.homAddEquiv) (e₃ := CategoryTheory.Abelian.Ext.homAddEquiv) (H := this)
  all_goals ext x; apply CategoryTheory.Abelian.Ext.hom_comp_singleFunctor_map_shift (C := C)

