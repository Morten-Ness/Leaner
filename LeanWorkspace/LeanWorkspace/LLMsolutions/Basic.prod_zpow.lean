FAIL
import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_zpow {N} [DivisionCommMonoid N] [Fintype α] (f : α →₀ ℤ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a := by
  classical
  rw [Finsupp.prod]
  symm
  refine Finset.prod_subset ?_ ?_
  · intro a ha
    simpa using ha
  · intro a ha hs
    have hfa : f a = 0 := by
      exact Finsupp.not_mem_support_iff.mp hs
    simp [hfa]
