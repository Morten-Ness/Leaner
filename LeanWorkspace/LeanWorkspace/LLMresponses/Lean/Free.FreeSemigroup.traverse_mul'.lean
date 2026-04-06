import Mathlib

variable {α : Type u}

variable {β : Type u}

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

variable [LawfulApplicative m]

theorem traverse_mul' :
    Function.comp (traverse F) ∘ (HMul.hMul : FreeSemigroup α → FreeSemigroup α → FreeSemigroup α) =
      fun x y ↦ (· * ·) <$> traverse F x <*> traverse F y := by
  funext x y
  induction x <;> induction y <;> simp [Function.comp, FreeSemigroup.traverse]
