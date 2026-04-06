FAIL
import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem linearMap_ext {N} [CommSemiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
    [Module S R] [Module S A] [Module S N] ⦃f g : Unitization R A →ₗ[S] N⦄
    (hl : ∀ r, f (Unitization.inl r) = g (Unitization.inl r)) (hr : ∀ a : A, f a = g a) : f = g := by
  ext x
  exact Unitization.induction_on x (fun r => hl r) (fun a => hr a) (fun x y hx hy => by rw [map_add, map_add, hx, hy])
