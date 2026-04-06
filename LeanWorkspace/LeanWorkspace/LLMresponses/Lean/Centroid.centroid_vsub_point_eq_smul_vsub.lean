FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem centroid_vsub_point_eq_smul_vsub [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.points i = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  classical
  let p : P := s.points i
  let t : Affine.Simplex k V n := s.map (AffineMap.constVAdd k V (-ᵥ p))
  have hcentroid :
      t.centroid = s.centroid -ᵥ p := by
    simp [t, p]
  have hpoint :
      t.points i = 0 := by
    simp [t, p]
  have hface :
      t.faceOppositeCentroid i = s.faceOppositeCentroid i -ᵥ s.centroid + t.centroid := by
    rw [hcentroid]
    simpa [t, p, vadd_vsub_assoc]
  have hsum := t.centroid_eq_affineCombination_of_pointWeights_eq_one
    (fun j => if j = i then (0 : k) else (1 : k) / n)
  simp only [t, hpoint, Finset.sum_ite_eq, Finset.mem_univ, if_true, inv_zero, zero_mul,
    if_false] at hsum
  have hweights : ∑ j : Fin (n + 1), (if j = i then (0 : k) else (1 : k) / n) = (1 : k) := by
    rw [Finset.sum_ite_eq, Finset.sum_const_zero, zero_add]
    have : ∑ x : Fin n, (1 : k) / n = (n : k) * ((1 : k) / n) := by
      simp
    simpa [this, mul_inv_cancel₀ (show (n : k) ≠ 0 by exact_mod_cast NeZero.ne n)]
      using Affine.Simplex.sum_eq_card_nsmul ((1 : k) / n) (Fin n)
  have hsum' := t.centroid_eq_affineCombination_of_pointWeights_eq_one
    (fun j => if j = i then (0 : k) else (1 : k) / n) hweights
  clear hsum hweights
  rw [hcentroid, hpoint] at hsum'
  simp only [AffineMap.lineMap_apply_module, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, if_false] at hsum'
  simpa [hface, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, smul_smul]
    using hsum'.symm
