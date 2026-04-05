import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

theorem exists_of [Nonempty ι] [IsDirectedOrder ι] (z : Ring.DirectLimit G f) :
    ∃ i x, of G f i x = z := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine z.induction_on ⟨Classical.arbitrary ι, -1, by simp; rfl⟩ (fun ⟨i, x⟩ ↦ ⟨i, x, rfl⟩) ?_ ?_
    <;> rintro x' y' ⟨i, x, hx⟩ ⟨j, y, hy⟩ <;> have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  · exact ⟨k, f i k hik x + f j k hjk y, by rw [map_add, of_f, of_f, hx, hy]; rfl⟩
  · exact ⟨k, f i k hik x * f j k hjk y, by rw [map_mul, of_f, of_f, hx, hy]; rfl⟩

