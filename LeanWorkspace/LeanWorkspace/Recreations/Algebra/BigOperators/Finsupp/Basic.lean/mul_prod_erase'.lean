import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem mul_prod_erase' (f : α →₀ M) (y : α) (g : α → M → N) (hg : ∀ i : α, g i 0 = 1) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  classical
    by_cases hyf : y ∈ f.support
    · exact Finsupp.mul_prod_erase f y g hyf
    · rw [notMem_support_iff.mp hyf, hg y, erase_of_notMem_support hyf, one_mul]

