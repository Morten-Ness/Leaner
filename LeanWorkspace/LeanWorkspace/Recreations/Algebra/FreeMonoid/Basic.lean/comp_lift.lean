import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem comp_lift (g : M →* N) (f : α → M) : g.comp (FreeMonoid.lift f) = FreeMonoid.lift (g ∘ f) := by
  ext
  simp

