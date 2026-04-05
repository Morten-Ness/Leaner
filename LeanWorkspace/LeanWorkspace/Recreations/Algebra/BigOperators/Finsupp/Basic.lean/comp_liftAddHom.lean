import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem comp_liftAddHom [AddZeroClass M] [AddCommMonoid N] [AddCommMonoid P] (g : N →+ P)
    (f : α → M →+ N) :
    g.comp ((Finsupp.liftAddHom (α := α) (M := M) (N := N)) f) =
      (Finsupp.liftAddHom (α := α) (M := M) (N := P)) fun a => g.comp (f a) :=
  Finsupp.liftAddHom.symm_apply_eq.1 <|
    funext fun a => by
      rw [Finsupp.liftAddHom_symm_apply, AddMonoidHom.comp_assoc, Finsupp.liftAddHom_comp_single]

