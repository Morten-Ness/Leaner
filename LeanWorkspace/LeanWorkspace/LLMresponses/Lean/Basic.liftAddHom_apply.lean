import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem liftAddHom_apply [AddZeroClass M] [AddCommMonoid N] (F : α → M →+ N) (f : α →₀ M) :
    (Finsupp.liftAddHom F) f = f.sum fun a b => F a b := rfl
