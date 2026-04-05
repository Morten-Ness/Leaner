import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_def [DecidableEq R] (p : R[X]) [Decidable (p = 0)] :
    p.roots = if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h) := by
  rename_i iR ip0
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  obtain rfl := Subsingleton.elim ip0 (Classical.dec (p = 0))
  rfl

