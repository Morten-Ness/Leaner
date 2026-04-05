import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem hom_eq ⦃f g : FreeMonoid α →* M⦄ (h : ∀ x, f (FreeMonoid.of x) = g (FreeMonoid.of x)) : f = g := MonoidHom.ext fun l ↦ FreeMonoid.recOn l (f.map_one.trans g.map_one.symm)
    (fun x xs hxs ↦ by simp only [h, hxs, map_mul])

