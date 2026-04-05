import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

include hS in
theorem contravariant_sequence_exact₂' (n : ℕ) :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n)))
      (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n))) (by
        ext
        dsimp
        simp only [mk₀_comp_mk₀_assoc, ShortComplex.zero, mk₀_zero, zero_comp])).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₂ _
    (op_distinguished _ hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := CategoryTheory.Abelian.Ext.homAddEquiv)
    (e₂ := CategoryTheory.Abelian.Ext.homAddEquiv) (e₃ := CategoryTheory.Abelian.Ext.homAddEquiv) (H := this)
  all_goals ext; apply CategoryTheory.Abelian.Ext.singleFunctor_map_comp_hom (C := C)

