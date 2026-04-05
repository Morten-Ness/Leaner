import Mathlib

variable {M : Type*} [Monoid M] [HasDistribNeg M] {a b : M}

theorem neg_left_iff : Associated (-a) b ↔ Associated a b := ⟨fun h ↦ Associated.neg_neg _root_ a ▸ Associated.neg_left h, fun h ↦ Associated.neg_left h⟩

