import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable {A B : Type*} [CommRing A] [CommRing B]

theorem count_map_roots_of_injective [IsDomain A] [DecidableEq B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  by_cases hp0 : p = 0
  · simp only [hp0, Polynomial.roots_zero, Multiset.map_zero, Multiset.count_zero, Polynomial.map_zero,
      rootMultiplicity_zero, le_refl]
  · exact Polynomial.count_map_roots ((Polynomial.map_ne_zero_iff hf).mpr hp0) b

