import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

theorem precomp_mk₀_injective_of_epi (L : C) {M N : C} (g : M ⟶ N) [hg : Epi g] :
    Function.Injective ((CategoryTheory.Abelian.Ext.mk₀ g).precomp L (zero_add 0)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨f, rfl⟩ := CategoryTheory.Abelian.Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_epi g] using hx

