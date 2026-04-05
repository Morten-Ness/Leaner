import Mathlib

theorem expChar_center_iff {R : Type u} [Ring R] {p : ℕ} :
    ExpChar (Subring.center R) p ↔ ExpChar R p := (algebraMap (Subring.center R) R).expChar_iff Subtype.val_injective p

