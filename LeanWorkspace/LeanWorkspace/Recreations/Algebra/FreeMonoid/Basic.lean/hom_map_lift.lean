import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem hom_map_lift (g : M →* N) (f : α → M) (x : FreeMonoid α) : g (FreeMonoid.lift f x) = FreeMonoid.lift (g ∘ f) x := DFunLike.ext_iff.1 (FreeMonoid.comp_lift g f) x

