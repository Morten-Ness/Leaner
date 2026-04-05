import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

theorem mono_postcomp_mk₀_of_mono (L : C) {M N : C} (f : M ⟶ N) [hf : Mono f] :
    Mono (AddCommGrpCat.ofHom <| (CategoryTheory.Abelian.Ext.mk₀ f).postcomp L (add_zero 0)) := (AddCommGrpCat.mono_iff_injective _).mpr (CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono L f)

