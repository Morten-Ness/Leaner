import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem affineSpan_range_medial [CharZero k] (s : Affine.Simplex k P n) :
    affineSpan k (Set.range (s.medial.points)) = affineSpan k (Set.range (s.points)) := by
  have hmem1 : s.medial.points 0 ∈ affineSpan k (Set.range s.medial.points) :=
    mem_affineSpan _ (by simp)
  have hmem2 : s.medial.points 0 ∈ affineSpan k (Set.range s.points) := by
    apply Set.mem_of_mem_of_subset (Affine.Simplex.faceOppositeCentroid_mem_affineSpan_face s 0)
    exact affineSpan_mono k (by simp)
  rw [eq_iff_direction_eq_of_mem hmem1 hmem2]
  simp_rw [direction_affineSpan, vectorSpan_def]
  suffices Set.range s.medial.points -ᵥ Set.range s.medial.points
    = (-n : k)⁻¹ • (Set.range s.points -ᵥ Set.range s.points) by
    rw [this, Submodule.span_smul_eq_of_isUnit]
    simpa using NeZero.ne n
  ext v
  suffices (∃ a b, (n : k)⁻¹ • (s.points b -ᵥ s.points a) = v) ↔
    ∃ a b, -((n : k)⁻¹ • (s.points a -ᵥ s.points b)) = v by
    simpa [Set.mem_vsub, Set.mem_smul_set, Affine.Simplex.medial_points,
      Affine.Simplex.faceOppositeCentroid_vsub_faceOppositeCentroid]
  congrm ∃ a b, ?_ = v
  simp [← smul_neg]

