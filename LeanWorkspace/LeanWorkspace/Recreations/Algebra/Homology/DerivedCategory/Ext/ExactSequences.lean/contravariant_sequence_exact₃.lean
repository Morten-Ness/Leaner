import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

theorem contravariant_sequence_exact₃ {n₁ : ℕ} (x₃ : CategoryTheory.Abelian.Ext S.X₃ Y n₁)
    (hx₃ : (mk₀ S.g).comp x₃ (zero_add n₁) = 0) {n₀ : ℕ} (hn₀ : 1 + n₀ = n₁) :
    ∃ (x₁ : CategoryTheory.Abelian.Ext S.X₁ Y n₀), hS.extClass.comp x₁ hn₀ = x₃ := by
  have := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃' hS Y n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

