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

theorem congr_apply_of (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
    {i : ι} (g : G i) :
    Module.DirectLimit.congr e he (Module.DirectLimit.of _ _ G f i g) = Module.DirectLimit.of _ _ G' f' i (e i g) := map_apply_of _ he _

