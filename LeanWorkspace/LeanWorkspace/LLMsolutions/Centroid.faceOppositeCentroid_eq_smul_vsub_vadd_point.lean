FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_eq_smul_vsub_vadd_point [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n : k)⁻¹ • (s.centroid -ᵥ s.points i) +ᵥ s.centroid := by
  rw [Affine.Simplex.faceOppositeCentroid]
  let w : Fin (n + 1) → k := fun j => if j = i then 0 else (n : k)⁻¹
  have hw_sum : ∑ j, w j = (1 : k) := by
    classical
    rw [show (∑ j : Fin (n + 1), w j) = ∑ j in ({i}ᶜ : Finset (Fin (n + 1))), (n : k)⁻¹ by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro j hj
        simp only [Finset.mem_compl, Finset.mem_singleton] at hj
        simp [w, hj]
      · intro j hj1 hj2
        simp only [Finset.mem_univ, Finset.mem_compl, Finset.mem_singleton, true_and] at hj2
        simp [w, hj2]]
    have hcard : ({i}ᶜ : Finset (Fin (n + 1))).card = n := by
      simpa using Finset.card_compl_singleton i
    rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat]
    field_simp [Nat.cast_ne_zero]
  have hcent :
      s.centroid =
        AffineMap.lineMap (s.points i) (s.faceOppositeCentroid i) ((n : k) / (n + 1 : ℕ) : k) := by
    rw [Affine.Simplex.centroid_eq_affineCombination]
    congr with j
    by_cases hji : j = i
    · subst hji
      simp [w]
    · simp [w, hji]
    · simpa [w] using hw_sum
  have hn0 : (n : k) ≠ 0 := Nat.cast_ne_zero n
  have hnp10 : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero (n + 1)
  have hfrac : ((n : k) / (n + 1 : ℕ) : k) ≠ 1 := by
    intro h
    have : ((n : k) : k) = (n + 1 : ℕ) := by
      exact (div_eq_iff hnp10).mp h
    norm_num at this
  have hline :=
    AffineMap.lineMap_apply_module (s.points i) (s.faceOppositeCentroid i) ((n : k) / (n + 1 : ℕ) : k)
  rw [hline] at hcent
  have hvsub :
      s.centroid -ᵥ s.points i =
        (((n : k) / (n + 1 : ℕ) : k)) • (s.faceOppositeCentroid i -ᵥ s.points i) := by
    simpa [vsub_vadd, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcent
  have hinv : (((n : k) / (n + 1 : ℕ) : k))⁻¹ = ((n + 1 : ℕ) : k) / (n : k) := by
    field_simp [hn0, hnp10]
  have hvsub' :
      s.faceOppositeCentroid i -ᵥ s.points i =
        (((n + 1 : ℕ) : k) / (n : k)) • (s.centroid -ᵥ s.points i) := by
    rw [hvsub]
    field_simp [hn0, hnp10]
  have hdecomp :
      s.faceOppositeCentroid i -ᵥ s.points i =
        (s.centroid -ᵥ s.points i) + (s.faceOppositeCentroid i -ᵥ s.centroid) := by
    simpa using vsub_assoc (s.faceOppositeCentroid i) s.centroid (s.points i)
  have hfinal :
      s.faceOppositeCentroid i -ᵥ s.centroid =
        (n : k)⁻¹ • (s.centroid -ᵥ s.points i) := by
    rw [← add_right_inj (-(s.centroid -ᵥ s.points i))]
    rw [add_assoc, add_left_neg, zero_add]
    rw [hvsub', hdecomp]
    have hcalc : (((n + 1 : ℕ) : k) / (n : k)) = (1 : k) + (n : k)⁻¹ := by
      field_simp [hn0]
      ring
    rw [hcalc]
    simp [add_smul]
  exact eq_of_vsub_eq_vsub_right <| by simpa using hfinal.symm
