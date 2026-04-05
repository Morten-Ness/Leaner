import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

theorem mono_precomp_mk₀_of_epi (L : C) {M N : C} (g : M ⟶ N) [hg : Epi g] :
    Mono (AddCommGrpCat.ofHom <| (CategoryTheory.Abelian.Ext.mk₀ g).precomp L (zero_add 0)) := (AddCommGrpCat.mono_iff_injective _).mpr (CategoryTheory.Abelian.Ext.precomp_mk₀_injective_of_epi L g)

