import Mathlib

variable {ι A B R : Type*} {κ : ι → Type*}

theorem quasispectrum.mem_iff_of_isUnit [CommSemiring R] [NonUnitalRing A]
    [Module R A] {a : A} {r : R} (hr : IsUnit r) :
    r ∈ quasispectrum R a ↔ ¬ IsQuasiregular (-(hr.unit⁻¹ • a)) := ⟨fun h => h hr, fun h _ => h⟩

