import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {A : Type*} [CommRing A] [IsDomain A] [Module A M₂] (B₃ : BilinForm A M₂)

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem _root_.Matrix.separatingLeft_toBilin_iff {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂) :
    (Matrix.toBilin b M).SeparatingLeft ↔ M.SeparatingLeft := Matrix.separatingLeft_toLinearMap₂_iff b b

