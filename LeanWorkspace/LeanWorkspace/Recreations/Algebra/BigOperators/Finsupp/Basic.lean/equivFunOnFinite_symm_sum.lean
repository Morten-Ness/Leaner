import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem equivFunOnFinite_symm_sum [Fintype α] [AddCommMonoid M] (f : α → M) :
    ((equivFunOnFinite.symm f).sum fun _ n ↦ n) = ∑ a, f a := by
  rw [Finsupp.equivFunOnFinite_symm_eq_sum, sum_fintype _ _ fun _ ↦ rfl, Finsupp.coe_univ_sum_single]

