import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable (G) [∀ i, AddCommMonoid (G i)]

variable (f : ∀ i j, i ≤ j → G i →+ G j)

variable [DecidableEq ι]

variable (P : Type*) [AddCommMonoid P]

variable (g : ∀ i, G i →+ P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem lift_of (i x) : AddCommGroup.DirectLimit.lift G f P g Hg (AddCommGroup.DirectLimit.of G f i x) = g i x := Module.DirectLimit.lift_of
    -- Note: had to make these arguments explicit https://github.com/leanprover-community/mathlib4/pull/8386
    (f := fun i j hij ↦ (f i j hij).toNatLinearMap)
    (fun i ↦ (g i).toNatLinearMap)
    Hg
    x

