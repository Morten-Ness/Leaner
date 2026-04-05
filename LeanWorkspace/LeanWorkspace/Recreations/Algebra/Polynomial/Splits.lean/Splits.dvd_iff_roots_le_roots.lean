import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.dvd_iff_roots_le_roots (hf : f.Splits) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    f ∣ g ↔ f.roots ≤ g.roots := ⟨roots.le_of_dvd hg0, hf.dvd_of_roots_le_roots hf0⟩

