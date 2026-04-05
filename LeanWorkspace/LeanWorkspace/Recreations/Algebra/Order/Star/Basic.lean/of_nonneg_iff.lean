import Mathlib

open scoped NNRat

variable {R A : Type*}

theorem of_nonneg_iff [NonUnitalRing R] [PartialOrder R] [StarRing R]
    (h_add : ∀ {x y : R}, x ≤ y → ∀ z, z + x ≤ z + y)
    (h_nonneg_iff : ∀ x : R, 0 ≤ x ↔ x ∈ AddSubmonoid.closure (Set.range fun s : R => star s * s)) :
    StarOrderedRing R where
  le_iff x y := by
    have : AddLeftMono R := ⟨fun _ _ _ h => h_add h _⟩
    simpa only [← sub_eq_iff_eq_add', sub_nonneg, exists_eq_right'] using h_nonneg_iff (y - x)

