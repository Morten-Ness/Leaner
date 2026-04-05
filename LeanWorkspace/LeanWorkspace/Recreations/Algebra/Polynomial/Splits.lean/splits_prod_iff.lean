import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem splits_prod_iff {ι : Type*} {f : ι → R[X]} {s : Finset ι} (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ x ∈ s, f x).Splits ↔ ∀ x ∈ s, (f x).Splits := ⟨fun h _ hx ↦ h.of_dvd (Finset.prod_ne_zero_iff.mpr hf) (Finset.dvd_prod_of_mem f hx),
    Polynomial.Splits.prod⟩

