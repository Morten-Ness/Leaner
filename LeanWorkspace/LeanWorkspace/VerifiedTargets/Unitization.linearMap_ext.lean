import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem linearMap_ext {N} [CommSemiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
    [Module S R] [Module S A] [Module S N] ⦃f g : Unitization R A →ₗ[S] N⦄
    (hl : ∀ r, f (Unitization.inl r) = g (Unitization.inl r)) (hr : ∀ a : A, f a = g a) : f = g := (Unitization.linearEquiv S R A).arrowCongr (.refl ..) |>.injective <|
    LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

