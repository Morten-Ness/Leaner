import Mathlib

variable {M : Type*} [Monoid M] [HasDistribNeg M] {a b : M}

theorem neg_right_iff : Associated a (-b) ↔ Associated a b := ⟨fun h ↦ Associated.neg_neg _root_ b ▸ Associated.neg_right h, fun h ↦ Associated.neg_right h⟩

