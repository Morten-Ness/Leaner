import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (P : Type*) [CommRing P]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

variable [DirectedSystem G fun i j h ↦ f' i j h] [IsDirectedOrder ι]

theorem of.zero_exact {i x} (hix : of G (f' · · ·) i x = 0) :
    ∃ (j : _) (hij : i ≤ j), f' i j hij x = 0 := by
  have := Nonempty.intro i
  apply_fun Ring.DirectLimit.ringEquiv _ _ at hix
  rwa [map_zero, Ring.DirectLimit.ringEquiv_of, Ring.DirectLimit.exists_eq_zero] at hix

