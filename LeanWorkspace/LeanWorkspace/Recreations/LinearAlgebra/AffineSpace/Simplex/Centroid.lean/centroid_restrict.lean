import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_restrict [CharZero k] {n : ℕ} (s : Affine.Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).centroid = s.centroid := by
  rw [eq_comm]
  haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  have hf : Function.Injective (S.subtype) := by
    simp only [coe_subtype, Subtype.val_injective]
  exact (s.restrict S hS).centroid_map S.subtype hf

