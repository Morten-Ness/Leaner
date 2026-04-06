FAIL
import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_pow [Fintype α] (f : α →₀ ℕ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a := by
  classical
  rw [Finsupp.prod]
  refine (Finset.prod_subset (s₁ := f.support) (s₂ := Finset.univ) ?_ ?_).symm
  · intro a ha
    exact Finset.mem_univ a
  · intro a ha_univ ha_support
    rw [Finsupp.mem_support_iff] at ha_support
    simp [ha_support]
