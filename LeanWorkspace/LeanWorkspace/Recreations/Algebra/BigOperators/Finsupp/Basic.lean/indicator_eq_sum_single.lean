import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem indicator_eq_sum_single [AddCommMonoid M] (s : Finset α) (f : α → M) :
    indicator s (fun x _ ↦ f x) = ∑ x ∈ s, single x (f x) := (Finsupp.indicator_eq_sum_attach_single _).trans <| sum_attach _ fun x ↦ single x (f x)

