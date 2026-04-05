import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable (G) [∀ i, AddCommMonoid (G i)]

variable (f : ∀ i j, i ≤ j → G i →+ G j)

variable [DecidableEq ι]

variable (P : Type*) [AddCommMonoid P]

variable (g : ∀ i, G i →+ P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem hom_ext {g₁ g₂ : AddCommGroup.DirectLimit G f →+ P} (h : ∀ i, g₁.comp (AddCommGroup.DirectLimit.of G f i) = g₂.comp (AddCommGroup.DirectLimit.of G f i)) :
    g₁ = g₂ := AddCon.hom_ext <| DirectSum.addHom_ext' h

