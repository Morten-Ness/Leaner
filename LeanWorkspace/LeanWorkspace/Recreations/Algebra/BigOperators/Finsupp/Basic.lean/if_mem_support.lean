import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem if_mem_support [DecidableEq α] {N : Type*} [Zero N] (f : α →₀ N) (a : α) :
    (if a ∈ f.support then f a else 0) = f a := by
  simp only [mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  exact fun h ↦ h.symm

