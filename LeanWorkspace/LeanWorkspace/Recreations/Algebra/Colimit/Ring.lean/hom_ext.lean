import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (P : Type*) [CommRing P]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem hom_ext {g₁ g₂ : Ring.DirectLimit G f →+* P} (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := Ideal.Quotient.ringHom_ext <| FreeCommRing.hom_ext fun ⟨i, x⟩ => congr($(h i) x)

