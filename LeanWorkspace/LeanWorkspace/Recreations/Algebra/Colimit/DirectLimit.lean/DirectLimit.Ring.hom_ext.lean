import Mathlib

variable {R ι : Type*} [Preorder ι] {G : ι → Type*}

variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}

variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]

variable [IsDirectedOrder ι]

variable [∀ i, NonAssocSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] [Nonempty ι]

variable (P : Type*) [NonAssocSemiring P]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem hom_ext {g₁ g₂ : DirectLimit G f →+* P} (h : ∀ i, g₁.comp (DirectLimit.Module.of G f i) = g₂.comp (DirectLimit.Module.of G f i)) :
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

