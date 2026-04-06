FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem affineIndependent_points_update_centroid [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    AffineIndependent k (Function.update s.points i s.centroid) := by
  classical
  rw [AffineIndependent]
  intro s' w hw0 hwv j hj
  by_cases hji : j = i
  · subst hji
    have hsum :
        ∑ x in s'.erase i, w x = -w i := by
      have h :=
        eq_neg_iff_add_eq_zero.mpr <| by
          rw [← Finset.sum_erase_add _ (Finset.mem_of_mem_erase hj), hw0]
      simpa [add_comm, add_left_comm, add_assoc] using h
    have hcentroid :
        s.centroid = (∑ j : Fin (n + 1), (1 : k))⁻¹ • ∑ j, s.points j := by
      simpa [Affine.Simplex.centroid, Finset.smul_sum] using rfl
    have hcard : (∑ j : Fin (n + 1), (1 : k)) = (n + 1 : k) := by
      simp
    have hne : (n + 1 : k) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    let w' : Fin (n + 1) → k := Function.update w i 0
    have hw'sum : ∑ j, w' j = 0 := by
      rw [Finset.sum_update_of_mem i (Finset.mem_univ i), hw0, add_right_neg]
    have hw'vsub : (Finset.univ.weightedVSub s.points) w' = 0 := by
      have huniv : s' = Finset.univ := by
        apply Finset.eq_univ_of_card
        exact le_antisymm (Finset.card_le_univ _) (by simp)
      subst huniv
      ext
      have h1 :
          (Finset.univ.weightedVSub (Function.update s.points i s.centroid)) w =
            (Finset.univ.weightedVSub s.points) w'
              + w i • (s.centroid -ᵥ s.points i) := by
        simp [w', Finset.weightedVSub, sub_eq_add_neg, Finset.sum_update_of_mem, vsub_eq_sub]
      have h2 :
          w i • (s.centroid -ᵥ s.points i) =
            (Finset.univ.weightedVSub s.points) (fun j => if j = i then w i * ((n + 1 : k)⁻¹ - 1) else w i * (n + 1 : k)⁻¹) := by
        ext
        simp [Affine.Simplex.centroid, Finset.weightedVSub, vsub_eq_sub, hne]
      rw [← hwv]
      sorry
    exact s.isAffineBasis.affineIndependent hw'sum hw'vsub i (Finset.mem_univ i)
  · have hs' : s'.erase i ⊆ Finset.univ := by simp
    sorry
