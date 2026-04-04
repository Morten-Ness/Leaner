import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_mem_affineSpan [CharZero k] {n : ℕ} (s : Affine.Simplex k P n) :
    s.centroid ∈ affineSpan k (Set.range s.points) := centroid_mem_affineSpan_of_card_eq_add_one k _ (card_fin (n + 1))

