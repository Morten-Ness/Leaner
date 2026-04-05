import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (P : Type*) [CommRing P]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem lift_comp_of (F : Ring.DirectLimit G f →+* P) :
    Ring.DirectLimit.lift G f _ (fun i ↦ F.comp <| of G f i) (fun i j hij x ↦ by simp) = F := by
  ext; simp

