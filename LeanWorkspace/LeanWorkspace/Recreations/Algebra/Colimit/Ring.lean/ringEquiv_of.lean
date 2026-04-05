import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (P : Type*) [CommRing P]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

variable [DirectedSystem G fun i j h ↦ f' i j h] [IsDirectedOrder ι]

theorem ringEquiv_of [Nonempty ι] {i g} : Ring.DirectLimit.ringEquiv G f' (of _ _ i g) = ⟦⟨i, g⟩⟧ := by
  simp [Ring.DirectLimit.ringEquiv]; rfl

