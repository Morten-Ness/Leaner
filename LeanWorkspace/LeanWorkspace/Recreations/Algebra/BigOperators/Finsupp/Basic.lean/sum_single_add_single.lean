import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem sum_single_add_single (f₁ f₂ : ι) (g₁ g₂ : A) (F : ι → A → B) (H : f₁ ≠ f₂)
    (HF : ∀ f, F f 0 = 0) :
    sum (single f₁ g₁ + single f₂ g₂) F = F f₁ g₁ + F f₂ g₂ := by
  classical
  simp [sum_of_support_subset _ support_single_add_single_subset, single_apply, H, HF, H.symm]

