import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_dvd_prod_of_subset_of_dvd [Zero M] [CommMonoid N] {f1 f2 : α →₀ M}
    {g1 g2 : α → M → N} (h1 : f1.support ⊆ f2.support)
    (h2 : ∀ a : α, a ∈ f1.support → g1 a (f1 a) ∣ g2 a (f2 a)) : f1.prod g1 ∣ f2.prod g2 := by
  classical
    simp only [Finsupp.prod]
    rw [← sdiff_union_of_subset h1, prod_union sdiff_disjoint]
    apply dvd_mul_of_dvd_right
    apply prod_dvd_prod_of_dvd
    exact h2

