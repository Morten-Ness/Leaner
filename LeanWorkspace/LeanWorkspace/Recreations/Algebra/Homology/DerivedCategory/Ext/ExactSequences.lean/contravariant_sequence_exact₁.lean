import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

theorem contravariant_sequence_exact₁ {n₀ : ℕ} (x₁ : CategoryTheory.Abelian.Ext S.X₁ Y n₀) {n₁ : ℕ} (hn₁ : 1 + n₀ = n₁)
    (hx₁ : hS.extClass.comp x₁ hn₁ = 0) :
    ∃ (x₂ : CategoryTheory.Abelian.Ext S.X₂ Y n₀), (mk₀ S.f).comp x₂ (zero_add n₀) = x₁ := by
  have := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁' hS Y n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

