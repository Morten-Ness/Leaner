import Mathlib

theorem charP_center_iff {R : Type u} [Ring R] {p : ℕ} :
    CharP (Subring.center R) p ↔ CharP R p := (algebraMap (Subring.center R) R).charP_iff Subtype.val_injective p

