import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem liftAddHom_singleAddHom [AddCommMonoid M] :
    (Finsupp.liftAddHom (α := α) (M := M) (N := α →₀ M)) (singleAddHom : α → M →+ α →₀ M) =
      AddMonoidHom.id _ :=
  Finsupp.liftAddHom.toEquiv.apply_eq_iff_eq_symm_apply.2 rfl

