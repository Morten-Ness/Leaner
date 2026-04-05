import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.of_dvd (hg : Polynomial.Splits g) (hg₀ : g ≠ 0) (hfg : f ∣ g) : Polynomial.Splits f := by
  obtain ⟨g, rfl⟩ := hfg
  exact ((Polynomial.splits_mul_iff (by simp_all) (by simp_all)).mp hg).1

