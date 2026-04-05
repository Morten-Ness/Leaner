import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem lift_injective [IsDirectedOrder ι]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (Module.DirectLimit.lift R ι G f g Hg) := by
  cases isEmpty_or_nonempty ι
  · apply Function.injective_of_subsingleton
  intro z w eq
  obtain ⟨i, x, y, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  simp_rw [lift_of] at eq
  rw [injective _ eq]

