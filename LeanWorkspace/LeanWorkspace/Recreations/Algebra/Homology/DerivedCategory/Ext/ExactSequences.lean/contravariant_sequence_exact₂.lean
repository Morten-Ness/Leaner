import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

include hS in
theorem contravariant_sequence_exact₂ {n : ℕ} (x₂ : CategoryTheory.Abelian.Ext S.X₂ Y n)
    (hx₂ : (mk₀ S.f).comp x₂ (zero_add n) = 0) :
    ∃ (x₁ : CategoryTheory.Abelian.Ext S.X₃ Y n), (mk₀ S.g).comp x₁ (zero_add n) = x₂ := by
  have := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂' hS Y n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

