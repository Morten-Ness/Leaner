import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem sum_ite_self_eq [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (f.sum fun x v => ite (a = x) v 0) = f a := by
  simp_all

