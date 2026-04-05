import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_embDomain [Zero M] [CommMonoid N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
    (v.embDomain f).prod g = v.prod fun a b => g (f a) b := by
  rw [Finsupp.prod, Finsupp.prod, support_embDomain, Finset.prod_map]
  simp_rw [embDomain_apply_self]

