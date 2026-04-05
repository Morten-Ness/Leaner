import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {n} [Fintype n]

theorem diagonal_transvection_induction_of_det_ne_zero (P : Matrix n n 𝕜 → Prop) (M : Matrix n n 𝕜)
    (hMdet : Matrix.TransvectionStruct.det M ≠ 0) (hdiag : ∀ D : n → 𝕜, Matrix.TransvectionStruct.det (diagonal D) ≠ 0 → P (diagonal D))
    (htransvec : ∀ t : TransvectionStruct n 𝕜, P t.toMatrix)
    (hmul : ∀ A B, Matrix.TransvectionStruct.det A ≠ 0 → Matrix.TransvectionStruct.det B ≠ 0 → P A → P B → P (A * B)) : P M := by
  let Q : Matrix n n 𝕜 → Prop := fun N => Matrix.TransvectionStruct.det N ≠ 0 ∧ P N
  have : Q M := by
    apply Matrix.diagonal_transvection_induction Q M
    · grind
    · intro t
      exact ⟨by simp, htransvec t⟩
    · intro A B QA QB
      exact ⟨by simp [QA.1, QB.1], hmul A B QA.1 QB.1 QA.2 QB.2⟩
  exact this.2

