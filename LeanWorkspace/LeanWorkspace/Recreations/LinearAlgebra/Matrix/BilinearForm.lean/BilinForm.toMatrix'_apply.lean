import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o]

theorem BilinForm.toMatrix'_apply (B : BilinForm R₁ (n → R₁)) (i j : n) :
    BilinForm.toMatrix' B i j = B (Pi.single i 1) (Pi.single j 1) := LinearMap.toMatrix₂'_apply _ _ _

