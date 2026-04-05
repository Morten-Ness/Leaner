import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

include hS in
theorem covariant_sequence_exact₂ {n : ℕ} (x₂ : CategoryTheory.Abelian.Ext X S.X₂ n)
    (hx₂ : x₂.comp (mk₀ S.g) (add_zero n) = 0) :
    ∃ (x₁ : CategoryTheory.Abelian.Ext X S.X₁ n), x₁.comp (mk₀ S.f) (add_zero n) = x₂ := by
  have := CategoryTheory.Abelian.Ext.covariant_sequence_exact₂' X hS n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

