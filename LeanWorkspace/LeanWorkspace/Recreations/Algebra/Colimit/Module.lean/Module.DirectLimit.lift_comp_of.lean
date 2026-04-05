import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem lift_comp_of (F : Module.DirectLimit G f →ₗ[R] P) :
    Module.DirectLimit.lift R ι G f (fun i ↦ F.comp <| Module.DirectLimit.of R ι G f i) (fun i j hij x ↦ by simp) = F := by
  ext; simp

