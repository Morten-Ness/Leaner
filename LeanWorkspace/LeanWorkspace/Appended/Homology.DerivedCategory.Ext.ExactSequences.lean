import Mathlib

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

theorem postcomp_mk₀_injective_of_mono (L : C) {M N : C} (f : M ⟶ N) [hf : Mono f] :
    Function.Injective ((CategoryTheory.Abelian.Ext.mk₀ f).postcomp L (add_zero 0)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨g, rfl⟩ := CategoryTheory.Abelian.Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_mono f] using hx

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

theorem preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply
    [HasDerivedCategory.{w'} C] {X : C} {n₀ : ℕ} (x : CategoryTheory.Abelian.Ext X S.X₃ n₀)
    {n₁ : ℕ} (h : n₀ + 1 = n₁) :
    (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequenceδ
      hS.singleTriangle n₀ n₁ (by lia) x.hom =
        (x.comp hS.extClass h).hom := by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply,
    comp_hom, hS.extClass_hom, ShiftedHom.comp]
  rfl

end

section

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

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

theorem precomp_mk₀_injective_of_epi (L : C) {M N : C} (g : M ⟶ N) [hg : Epi g] :
    Function.Injective ((CategoryTheory.Abelian.Ext.mk₀ g).precomp L (zero_add 0)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨f, rfl⟩ := CategoryTheory.Abelian.Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_epi g] using hx

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

theorem singleFunctor_map_comp_hom [HasDerivedCategory.{w'} C]
    {X Y Z : C} (f : X ⟶ Y) {n : ℕ} (x : CategoryTheory.Abelian.Ext Y Z n) :
    (DerivedCategory.singleFunctor C 0).map f ≫ x.hom =
      ((mk₀ f).comp x (zero_add n)).hom := by
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp]

end
