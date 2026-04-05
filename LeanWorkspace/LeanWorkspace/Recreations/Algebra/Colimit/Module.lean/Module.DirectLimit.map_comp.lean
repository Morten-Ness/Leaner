import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variable {G' : ι → Type*} [∀ i, AddCommMonoid (G' i)] [∀ i, Module R (G' i)]

variable {f' : ∀ i j, i ≤ j → G' i →ₗ[R] G' j}

variable {G'' : ι → Type*} [∀ i, AddCommMonoid (G'' i)] [∀ i, Module R (G'' i)]

variable {f'' : ∀ i j, i ≤ j → G'' i →ₗ[R] G'' j}

theorem map_comp (g₁ : (i : ι) → G i →ₗ[R] G' i) (g₂ : (i : ι) → G' i →ₗ[R] G'' i)
    (hg₁ : ∀ i j h, g₁ j ∘ₗ f i j h = f' i j h ∘ₗ g₁ i)
    (hg₂ : ∀ i j h, g₂ j ∘ₗ f' i j h = f'' i j h ∘ₗ g₂ i) :
    (Module.DirectLimit.map g₂ hg₂ ∘ₗ Module.DirectLimit.map g₁ hg₁ :
      Module.DirectLimit G f →ₗ[R] Module.DirectLimit G'' f'') =
    (Module.DirectLimit.map (fun i ↦ g₂ i ∘ₗ g₁ i) fun i j h ↦ by
        rw [LinearMap.comp_assoc, hg₁ i, ← LinearMap.comp_assoc, hg₂ i, LinearMap.comp_assoc] :
      Module.DirectLimit G f →ₗ[R] Module.DirectLimit G'' f'') := by
  ext; simp

