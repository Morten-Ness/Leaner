FAIL
import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem smul_def (f : α → β → β) (l : FreeMonoid α) (b : β) :
    haveI : MulAction (FreeMonoid α) β where
      smul := FreeMonoid.recOn · id fun a _ g => f a ∘ g
      one_smul := rfl
      mul_smul := by
        intro x y b
        induction x using FreeMonoid.recOn with
        | nil =>
            rfl
        | cons a x ih =>
            simpa [Function.comp, ih]
    l • b = FreeMonoid.recOn l b fun a _ ih => f a ih := by
  letI : MulAction (FreeMonoid α) β where
    smul := FreeMonoid.recOn · id fun a _ g => f a ∘ g
    one_smul := rfl
    mul_smul := by
      intro x y b
      induction x using FreeMonoid.recOn with
      | nil =>
          rfl
      | cons a x ih =>
          simpa [Function.comp, ih]
  induction l using FreeMonoid.recOn with
  | nil =>
      rfl
  | cons a l ih =>
      simpa [Function.comp, ih] using (rfl : (FreeMonoid.of a * l) • b = f a (l • b))
