import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem affineSpan_insert_affineSpan (p : P) (ps : Set P) :
    affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (insert p ps) := by
  rw [Set.insert_eq, Set.insert_eq, AffineSubspace.span_union, AffineSubspace.span_union, AffineSubspace.affineSpan_coe]

