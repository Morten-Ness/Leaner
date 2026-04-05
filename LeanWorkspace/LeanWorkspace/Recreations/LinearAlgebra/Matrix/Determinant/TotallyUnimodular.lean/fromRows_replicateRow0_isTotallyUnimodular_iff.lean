import Mathlib

variable {m m' n n' R : Type*} [CommRing R]

theorem fromRows_replicateRow0_isTotallyUnimodular_iff (A : Matrix m n R) :
    (fromRows A (replicateRow m' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  classical
  refine Matrix.fromRows_isTotallyUnimodular_iff_rows <| fun _ _ => ?_
  inhabit n
  refine ⟨default, 0, ?_⟩
  ext x
  simp [Pi.single_apply]

