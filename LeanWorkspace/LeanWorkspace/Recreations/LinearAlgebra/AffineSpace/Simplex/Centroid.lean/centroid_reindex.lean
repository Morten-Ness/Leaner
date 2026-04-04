import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_reindex {m n : ℕ} (s : Affine.Simplex k P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).centroid = s.centroid := by
  rw [centroid, centroid]
  simp only [Affine.Simplex.centroid_eq_affineCombination]
  simp only [reindex]
  have h_eq : m = n := by simpa using Fintype.card_eq.2 ⟨e⟩
  subst h_eq
  convert Finset.univ.affineCombination_map e.toEmbedding _ _ <;> simp [Function.comp_assoc]

