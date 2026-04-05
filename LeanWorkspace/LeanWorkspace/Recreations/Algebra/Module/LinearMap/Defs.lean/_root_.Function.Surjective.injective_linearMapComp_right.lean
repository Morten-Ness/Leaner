import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂)

variable {f g} {f' : M₂ →ₛₗ[σ₂₃] M₃} {g' : M₁ →ₛₗ[σ₁₂] M₂}

theorem _root_.Function.Surjective.injective_linearMapComp_right (hg : Function.Surjective g) :
    Function.Injective fun f : M₂ →ₛₗ[σ₂₃] M₃ ↦ f.comp g := fun _ _ h ↦ LinearMap.ext <| hg.forall.2 (LinearMap.ext_iff.1 h)

