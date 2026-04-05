import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (P : Type*) [CommRing P]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

theorem of_injective [IsDirectedOrder ι] [DirectedSystem G fun i j h ↦ f' i j h]
    (hf : ∀ i j hij, Function.Injective (f' i j hij)) (i) :
    Function.Injective (of G (fun i j h ↦ f' i j h) i) := have := Nonempty.intro i
  ((Ring.DirectLimit.ringEquiv _ _).comp_injective _).mp
    fun _ _ eq ↦ Ring.DirectLimit.mk_injective f' hf _ (by simpa only [← Ring.DirectLimit.ringEquiv_of])

