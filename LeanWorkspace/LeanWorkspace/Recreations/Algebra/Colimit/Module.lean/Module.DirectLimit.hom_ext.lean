import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem hom_ext {g₁ g₂ : Module.DirectLimit G f →ₗ[R] P}
    (h : ∀ i, g₁ ∘ₗ Module.DirectLimit.of R ι G f i = g₂ ∘ₗ Module.DirectLimit.of R ι G f i) :
    g₁ = g₂ := LinearMap.toAddMonoidHom_injective <| AddCon.hom_ext <| DirectSum.addHom_ext' fun i =>
    congr($(h i).toAddMonoidHom)

