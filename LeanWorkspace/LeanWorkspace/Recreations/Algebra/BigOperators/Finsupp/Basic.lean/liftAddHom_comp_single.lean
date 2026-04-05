import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem liftAddHom_comp_single [AddZeroClass M] [AddCommMonoid N] (f : α → M →+ N) (a : α) :
    ((Finsupp.liftAddHom (α := α) (M := M) (N := N)) f).comp (singleAddHom a) = f a :=
  AddMonoidHom.ext fun b => Finsupp.liftAddHom_apply_single f a b

