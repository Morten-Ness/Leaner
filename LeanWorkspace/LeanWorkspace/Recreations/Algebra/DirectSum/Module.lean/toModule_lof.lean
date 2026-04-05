import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [DecidableEq ι]

variable {N : Type u₁} [AddCommMonoid N] [Module R N]

variable (φ : ∀ i, M i →ₗ[R] N)

theorem toModule_lof (i) (x : M i) : DirectSum.toModule R ι N φ (DirectSum.lof R ι M i x) = φ i x := toAddMonoid_of (fun i ↦ (φ i).toAddMonoidHom) i x

