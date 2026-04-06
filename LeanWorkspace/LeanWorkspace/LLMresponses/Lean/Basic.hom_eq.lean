FAIL
import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem hom_eq ⦃f g : FreeMonoid α →* M⦄ (h : ∀ x, f (FreeMonoid.of x) = g (FreeMonoid.of x)) : f = g := by
  ext x
  refine Quotient.inductionOn x ?_
  intro l
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      simpa [FreeMonoid.of, map_mul, h a, ih]
