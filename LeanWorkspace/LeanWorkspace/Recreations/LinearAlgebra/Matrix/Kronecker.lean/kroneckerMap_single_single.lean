import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem kroneckerMap_single_single
    [Zero α] [Zero β] [Zero γ] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (i₁ : l) (j₁ : m) (i₂ : n) (j₂ : p)
    (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (a : α) (b : β) :
    Matrix.kroneckerMap f (single i₁ j₁ a) (single i₂ j₂ b) = single (i₁, i₂) (j₁, j₂) (f a b) := by
  ext ⟨i₁', i₂'⟩ ⟨j₁', j₂'⟩
  dsimp [single]
  grind

