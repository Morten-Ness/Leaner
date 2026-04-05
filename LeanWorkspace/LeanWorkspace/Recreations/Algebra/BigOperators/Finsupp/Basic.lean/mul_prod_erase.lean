import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem mul_prod_erase (f : α →₀ M) (y : α) (g : α → M → N) (hyf : y ∈ f.support) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  classical
    rw [Finsupp.prod, Finsupp.prod, ← Finset.mul_prod_erase _ _ hyf, Finsupp.support_erase,
      Finset.prod_congr rfl]
    intro h hx
    rw [Finsupp.erase_ne (ne_of_mem_erase hx)]

