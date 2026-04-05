import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

theorem mk₀_bijective : Function.Bijective (CategoryTheory.Abelian.Ext.mk₀ (X := X) (Y := Y)) := by
  letI := HasDerivedCategory.standard C
  have h : (singleFunctor C 0).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  let e : (X ⟶ Y) ≃ CategoryTheory.Abelian.Ext X Y 0 :=
    (h.homEquiv.trans (ShiftedHom.homEquiv _ (by simp))).trans CategoryTheory.Abelian.Ext.homEquiv.symm
  have he : e.toFun = CategoryTheory.Abelian.Ext.mk₀ := by
    CategoryTheory.Abelian.Ext.ext f : 1
    dsimp [e]
    apply CategoryTheory.Abelian.Ext.homEquiv.injective
    apply (Equiv.apply_symm_apply _ _).trans
    symm
    apply SmallShiftedHom.equiv_mk₀
  rw [← he]
  exact e.bijective

