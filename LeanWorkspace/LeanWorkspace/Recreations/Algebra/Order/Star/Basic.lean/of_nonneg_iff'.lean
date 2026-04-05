import Mathlib

open scoped NNRat

variable {R A : Type*}

theorem of_nonneg_iff' [NonUnitalRing R] [PartialOrder R] [StarRing R]
    (h_add : ∀ {x y : R}, x ≤ y → ∀ z, z + x ≤ z + y)
    (h_nonneg_iff : ∀ x : R, 0 ≤ x ↔ ∃ s, x = star s * s) : StarOrderedRing R := StarOrderedRing.of_le_iff <| by
    have : AddLeftMono R := ⟨fun _ _ _ h => h_add h _⟩
    simpa [sub_eq_iff_eq_add', sub_nonneg] using fun x y => h_nonneg_iff (y - x)

