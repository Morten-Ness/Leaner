FAIL
import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem sum_sub_index [AddGroup β] [AddCommGroup γ] {f g : α →₀ β} {h : α → β → γ}
    (h_sub : ∀ a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).sum h = f.sum h - g.sum h := by
  classical
  have h_zero : ∀ a, h a 0 = 0 := by
    intro a
    have := h_sub a 0 0
    simpa using this
  have h_neg : ∀ a b, h a (-b) = -h a b := by
    intro a b
    have := h_sub a 0 b
    simpa [h_zero a] using this
  have h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂ := by
    intro a b₁ b₂
    calc
      h a (b₁ + b₂) = h a (b₁ - (-b₂)) := by simp
      _ = h a b₁ - h a (-b₂) := h_sub a b₁ (-b₂)
      _ = h a b₁ + h a b₂ := by rw [h_neg]; abel
  rw [sub_eq_add_neg, Finsupp.sum_add_index]
  · calc
      f.sum h + (-g).sum h = f.sum h + -(g.sum h) := by
        congr
        exact Finsupp.sum_neg_index h_neg
      _ = f.sum h - g.sum h := by simp [sub_eq_add_neg]
  · intro a ha
    exact h_zero a
  · intro a ha b₁ b₂
    exact h_add a b₁ b₂
