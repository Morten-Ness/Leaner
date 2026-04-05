import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem liftAddHom_apply_single [AddZeroClass M] [AddCommMonoid N] (f : α → M →+ N) (a : α)
    (b : M) : (Finsupp.liftAddHom (α := α) (M := M) (N := N)) f (single a b) = f a b :=
  sum_single_index (f a).map_zero

