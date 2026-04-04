import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_eq_affineCombination (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = ((Finset.affineCombination k {i}ᶜ s.points) fun _ ↦ (↑n)⁻¹) := by
  unfold Affine.Simplex.faceOppositeCentroid
  have : s.faceOpposite i = s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le]) := by rfl
  rw [this]
  unfold centroid
  rw [Affine.Simplex.face_centroid_eq_centroid, centroid_def, centroidWeights_eq_const, card_compl]
  simp only [Fintype.card_fin, card_singleton, add_tsub_cancel_right]
  rfl

