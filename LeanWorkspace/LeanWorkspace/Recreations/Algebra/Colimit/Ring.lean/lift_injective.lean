import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (P : Type*) [CommRing P]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem lift_injective [Nonempty ι] [IsDirectedOrder ι]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (Ring.DirectLimit.lift G f P g Hg) := by
  simp_rw [injective_iff_map_eq_zero] at injective ⊢
  intro z hz
  induction z using Ring.DirectLimit.induction_on with
  | ih _ g => rw [lift_of] at hz; rw [injective _ g hz, map_zero]

