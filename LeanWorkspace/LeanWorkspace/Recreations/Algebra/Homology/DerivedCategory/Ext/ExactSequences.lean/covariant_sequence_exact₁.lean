import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

theorem covariant_sequence_exact₁ {n₁ : ℕ} (x₁ : CategoryTheory.Abelian.Ext X S.X₁ n₁)
    (hx₁ : x₁.comp (mk₀ S.f) (add_zero n₁) = 0) {n₀ : ℕ} (hn₀ : n₀ + 1 = n₁) :
    ∃ (x₃ : CategoryTheory.Abelian.Ext X S.X₃ n₀), x₃.comp hS.extClass hn₀ = x₁ := by
  have := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁' X hS n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

