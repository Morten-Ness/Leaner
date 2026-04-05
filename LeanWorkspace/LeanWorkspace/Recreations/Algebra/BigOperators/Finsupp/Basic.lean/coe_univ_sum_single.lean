import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem coe_univ_sum_single [Fintype α] [AddCommMonoid M] (f : α → M) :
    ⇑(∑ a : α, single a (f a)) = f := congrArg _ (Finsupp.equivFunOnFinite_symm_eq_sum f).symm

