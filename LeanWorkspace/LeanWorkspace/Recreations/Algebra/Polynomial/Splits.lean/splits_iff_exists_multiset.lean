import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

theorem splits_iff_exists_multiset :
    Polynomial.Splits f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod := by
  refine Polynomial.splits_iff_exists_multiset'.trans ⟨?_, ?_⟩ <;>
    rintro ⟨m, hm⟩ <;> exact ⟨m.map (- ·), by simpa⟩

