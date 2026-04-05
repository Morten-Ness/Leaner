import Mathlib

variable {n R : Type*} [Ring R] [LinearOrder R]

variable {A : Matrix n n R}

theorem IsIrreducible.transpose (hA : IsIrreducible A) : IsIrreducible Aᵀ := by
  have hA_T_nonneg : ∀ i j, 0 ≤ Aᵀ i j := fun i j => by
    simpa [Matrix.transpose_apply] using hA.nonneg j i
  refine ⟨hA_T_nonneg, ?_⟩
  intro i j
  letI : Quiver n := Matrix.toQuiver A
  obtain ⟨p, hp_pos⟩ := hA.connected j i
  cases p with
  | nil =>
    simp at hp_pos
  | @cons b _ q e =>
    let qT := Matrix.transposePath (A := A) (q.cons e)
    letI : Quiver n := Matrix.toQuiver Aᵀ
    use qT
    simp [qT, Matrix.transposePath, Quiver.Path.length_comp, Quiver.Path.length_toPath]

