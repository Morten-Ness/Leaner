import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_notMem_affineSpan_of_ne_univ [CharZero k] (s : Affine.Simplex k P n)
    {t : Set (Fin (n + 1))} (ht : t ≠ Set.univ) :
    s.centroid ∉ affineSpan k (s.points '' t) := by
  intro h
  have hssubset : t ⊂ Set.univ := by grind
  obtain ⟨i, hi⟩ := Set.exists_of_ssubset hssubset
  rw [s.centroid_eq_affineCombination] at h
  set w := (Finset.centroidWeights k (Finset.univ : Finset (Fin (n + 1)))) with wdef
  have hw : ∑ i, w i = 1 := by rw [sum_centroidWeights_eq_one_of_nonempty _ _ (by simp)]
  have h1 := AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan s.independent hw h
    (by simp) hi.2
  have h2 : w i = (1 : k) / (n + 1) := by
    simp [wdef, centroidWeights_apply, card_univ, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
  simp only [h2, one_div, inv_eq_zero] at h1
  norm_cast at h1

