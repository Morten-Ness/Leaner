import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem single_sum [Zero M] [AddCommMonoid N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
    single a (s.sum f) = s.sum fun d c => single a (f d c) := Finsupp.single_finset_sum _ _ _

