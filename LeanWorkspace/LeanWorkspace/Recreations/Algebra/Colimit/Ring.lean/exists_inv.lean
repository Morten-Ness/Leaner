import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [Nonempty ι] [IsDirectedOrder ι] [∀ i, Field (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

theorem exists_inv {p : Ring.DirectLimit G f} : p ≠ 0 → ∃ y, p * y = 1 := Ring.DirectLimit.induction_on p fun i x H ↦
    ⟨Ring.DirectLimit.of G f i x⁻¹, by
      rw [← (Ring.DirectLimit.of _ _ _).map_mul,
        mul_inv_cancel₀ fun h : x = 0 ↦ H <| by rw [h, (Ring.DirectLimit.of _ _ _).map_zero],
        (Ring.DirectLimit.of _ _ _).map_one]⟩

