import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable (G) [∀ i, AddCommMonoid (G i)]

variable (f : ∀ i j, i ≤ j → G i →+ G j)

variable [DecidableEq ι]

variable (P : Type*) [AddCommMonoid P]

variable (g : ∀ i, G i →+ P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem lift_injective [IsDirectedOrder ι]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (AddCommGroup.DirectLimit.lift G f P g Hg) := Module.DirectLimit.lift_injective (f := fun i j hij ↦ (f i j hij).toNatLinearMap) _ Hg injective

