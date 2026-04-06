import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_unique [Unique α] {f : α →₀ M} {g : α → M → N} (h₁ : f default = 0 → g default 0 = 1) :
    f.prod g = g default (f default) := by
  classical
  by_cases h : f default = 0
  · have hs : f.support = ∅ := by
      ext a
      have : a = default := Subsingleton.elim _ _
      simp [Finsupp.mem_support_iff, this, h]
    rw [Finsupp.prod]
    simp [hs, h, h₁ h]
  · have hs : f.support = {default} := by
      ext a
      have : a = default := Subsingleton.elim _ _
      simp [Finsupp.mem_support_iff, this, h]
    rw [Finsupp.prod]
    simp [hs, h]
