FAIL
import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem hom_map_lift (g : M →* N) (f : α → M) (x : FreeMonoid α) : g (FreeMonoid.lift f x) = FreeMonoid.lift (g ∘ f) x := by
  induction x using FreeMonoid.recOn with
  | hnil =>
      simp [FreeMonoid.lift]
  | hcons a x ih =>
      simp [FreeMonoid.lift, ih, Function.comp]
