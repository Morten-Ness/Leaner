import Mathlib

variable {R ι : Type*} [Preorder ι] {G : ι → Type*}

variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}

variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]

variable [IsDirectedOrder ι]

variable [Semiring R] [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]

variable [∀ i j h, LinearMapClass (T h) R (G i) (G j)]

variable (R ι G f) [Nonempty ι]

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem hom_ext {g₁ g₂ : DirectLimit G f →ₗ[R] P}
    (h : ∀ i, g₁ ∘ₗ DirectLimit.Module.of R ι G f i = g₂ ∘ₗ DirectLimit.Module.of R ι G f i) : g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

