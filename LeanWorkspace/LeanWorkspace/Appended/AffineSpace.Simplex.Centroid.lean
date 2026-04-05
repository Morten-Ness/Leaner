import Mathlib

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem affineIndependent_points_update_centroid [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    AffineIndependent k (Function.update s.points i s.centroid) := by
  have : s.centroid ∉ affineSpan k (s.points '' {i}ᶜ) :=
    Affine.Simplex.centroid_notMem_affineSpan_of_ne_univ s (by simp)
  exact AffineIndependent.affineIndependent_update_of_notMem_affineSpan s.independent this

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_eq_of_range_eq {n : ℕ} {s₁ s₂ : Affine.Simplex k P n}
    (h : Set.range s₁.points = Set.range s₂.points) :
    Finset.univ.centroid k s₁.points = Finset.univ.centroid k s₂.points := by
  rw [← Set.image_univ, ← Set.image_univ, ← Finset.coe_univ] at h
  exact
    Finset.univ.centroid_eq_of_inj_on_of_image_eq k _
      (fun _ _ _ _ he => AffineIndependent.injective s₁.independent he)
      (fun _ _ _ _ he => AffineIndependent.injective s₂.independent he) h

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_eq_smul_sum_vsub_vadd [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = (n + 1 : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ s.points i := by
  rw [← Affine.Simplex.centroid_vsub_eq s, vsub_vadd]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem centroid_eq_smul_vsub_vadd_point [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.points i := by
  rw [← Affine.Simplex.centroid_vsub_point_eq_smul_vsub, vsub_vadd]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem centroid_mem_median [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.centroid ∈ s.median i := by
  rw [Affine.Simplex.median]
  have h : s.centroid = ((n : k) * (1 / (n + 1))) • (s.faceOppositeCentroid i -ᵥ s.points i)
    +ᵥ s.points i := by
    rw [eq_vadd_iff_vsub_eq, Affine.Simplex.centroid_vsub_point_eq_smul_vsub,
      Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_vsub, smul_smul, one_div, mul_assoc,
      inv_mul_cancel₀ (by norm_cast), mul_one]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem centroid_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.faceOppositeCentroid i = (n : k)⁻¹ • (s.points i -ᵥ s.centroid) := by
  rw [Affine.Simplex.point_vsub_centroid_eq_smul_vsub, smul_smul, inv_mul_cancel₀ (NeZero.ne (n : k)), one_smul]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem centroid_vsub_point_eq_smul_vsub [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.points i = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← neg_vsub_eq_vsub_rev, Affine.Simplex.point_vsub_centroid_eq_smul_vsub, ← neg_smul_neg,
    neg_vsub_eq_vsub_rev, ← neg_smul, neg_neg]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_weighted_vsub_eq_zero [CharZero k] (s : Affine.Simplex k P n) :
    ∑ i, (s.points i -ᵥ s.centroid) = 0 := by
  have h := Affine.Simplex.centroid_vsub_eq s s.centroid
  simp only [vsub_self] at h
  symm at h
  rw [smul_eq_zero_iff_right (inv_ne_zero (by norm_cast))] at h
  exact h

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_eq_smul_vsub_vadd_point [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n : k)⁻¹ • (s.centroid -ᵥ s.points i) +ᵥ s.centroid := by
  rw [Affine.Simplex.centroid_vsub_point_eq_smul_vsub, eq_vadd_iff_vsub_eq, smul_smul,
    inv_mul_cancel₀ (NeZero.ne (n : k)), one_smul]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_eq_sum_vsub_vadd [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ (s.points i) := by
  rw [← Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub s i, vsub_vadd]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_mem_affineSpan_face [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ affineSpan k (Set.range (s.faceOpposite i).points) := Affine.Simplex.centroid_mem_affineSpan (s.faceOpposite i)

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_mem_median (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ s.median i := by
  simp [Affine.Simplex.median, right_mem_affineSpan_pair]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_vsub_centroid_eq_smul_vsub [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.centroid = (n : k)⁻¹ • (s.centroid -ᵥ s.points i) := by
  rw [Affine.Simplex.centroid_vsub_point_eq_smul_vsub, smul_smul, inv_mul_cancel₀ (NeZero.ne (n : k)), one_smul]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_vsub_point_eq_smul_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.points i =
    (n + 1 : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← vsub_sub_vsub_cancel_right _ (s.centroid) (s.points i),
    Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, Affine.Simplex.centroid_vsub_eq,
    ← sub_smul, smul_smul]
  congr
  rw [mul_sub, add_mul, mul_inv_cancel₀ (NeZero.ne (n : k)), mul_inv_cancel₀ (by norm_cast),
    one_mul]
  grind

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem medial_map {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [CharZero k]
    {n : ℕ} [NeZero n] (s : Affine.Simplex k P n)
    (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).medial = s.medial.map f hf := by
  ext i
  simp [Affine.Simplex.medial_points]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem medial_reindex {m n : ℕ} [NeZero m] [NeZero n]
    [CharZero k] (s : Affine.Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).medial = s.medial.reindex e := by
  ext i
  simp [Affine.Simplex.medial_points]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem medial_restrict [CharZero k] (s : Affine.Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).medial = s.medial.restrict S (Affine.Simplex.affineSpan_range_medial s ▸ hS) := by
  haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  simp [Affine.Simplex.medial_points]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem median_eq_line_point_centroid [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.median i = line[k, s.points i, s.centroid] := by
  have h1 : s.median i ≤ line[k, s.points i, s.centroid] := by
    unfold Affine.Simplex.median
    apply affineSpan_pair_le_of_right_mem
    rw [Affine.Simplex.faceOppositeCentroid_eq_smul_vsub_vadd_point]
    have h : (n : k)⁻¹ • (s.centroid -ᵥ s.points i) = (-1 / n : k) • (s.points i -ᵥ s.centroid)
        := by
      rw [← neg_vsub_eq_vsub_rev]
      have : -(s.points i -ᵥ s.centroid) = (-1 : k) • (s.points i -ᵥ s.centroid) := by simp
      rw [this, smul_smul]
      congr 1
      rw [mul_neg_one, inv_eq_one_div, neg_div]
    rw [h]
    exact smul_vsub_rev_vadd_mem_affineSpan_pair _ _ _
  have h2 : line[k, s.points i, s.centroid] ≤ s.median i := by
    rw [Affine.Simplex.median]
    apply affineSpan_pair_le_of_right_mem
    exact Affine.Simplex.centroid_mem_median s i
  exact le_antisymm h1 h2

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem point_mem_median (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∈ s.median i := by
  simp [Affine.Simplex.median, left_mem_affineSpan_pair]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem point_vsub_centroid_eq_smul_vsub [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  symm
  rw [← vsub_sub_vsub_cancel_right _ _ (s.points i),
    Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub,
    Affine.Simplex.centroid_vsub_eq, ← neg_vsub_eq_vsub_rev,
    Affine.Simplex.centroid_vsub_eq, ← sub_smul, smul_smul, ← neg_smul]
  congr
  simp_rw [mul_sub, sub_eq_iff_eq_add, neg_add_eq_sub]
  symm
  rw [sub_eq_iff_eq_add, mul_inv_cancel₀ (NeZero.ne (n : k))]
  have : (↑n + (1 : k))⁻¹ = 1 * (↑n + (1 : k))⁻¹ := by simp
  nth_rw 2 [this]
  rw [← add_mul, mul_inv_cancel₀ (by norm_cast)]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem point_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i =
    (n + 1 : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  rw [← neg_vsub_eq_vsub_rev, Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_vsub, ← neg_smul,
    ← neg_smul_neg, neg_vsub_eq_vsub_rev, neg_neg]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem smul_centroid_vsub_point_eq_smul_faceOppositeCentroid_vsub_point [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    (n + 1 : k) • (s.centroid -ᵥ s.points i) =
    (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i) := by
  rw [Affine.Simplex.smul_faceOppositeCentroid_vsub_point_eq_sum_vsub s i,
    Affine.Simplex.smul_centroid_vsub_point_eq_sum_vsub s i]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem smul_centroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    ((n : k) + 1) • (s.centroid -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  rw [Affine.Simplex.centroid_eq_smul_sum_vsub_vadd s i, vadd_vsub, smul_smul, mul_inv_cancel₀, one_smul]
  norm_cast

end

section

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem smul_faceOppositeCentroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  simp [Affine.Simplex.faceOppositeCentroid_eq_sum_vsub_vadd, smul_smul, mul_inv_cancel₀ (NeZero.ne (n : k)),
    one_smul]

end
