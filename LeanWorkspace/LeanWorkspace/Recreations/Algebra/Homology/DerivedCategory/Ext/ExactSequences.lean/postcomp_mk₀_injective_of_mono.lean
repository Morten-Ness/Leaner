import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

theorem postcomp_mk₀_injective_of_mono (L : C) {M N : C} (f : M ⟶ N) [hf : Mono f] :
    Function.Injective ((CategoryTheory.Abelian.Ext.mk₀ f).postcomp L (add_zero 0)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨g, rfl⟩ := CategoryTheory.Abelian.Ext.addEquiv₀.symm.surjective x
  simpa [← cancel_mono f] using hx

