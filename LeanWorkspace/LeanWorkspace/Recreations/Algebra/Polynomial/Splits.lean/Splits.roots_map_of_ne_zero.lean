import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.roots_map_of_ne_zero {S : Type*} [CommRing S] [IsDomain S]
    {f : R[X]} (hf : Polynomial.Splits f) {φ : R →+* S} (hφ : f.map φ ≠ 0) :
    (f.map φ).roots = f.roots.map φ := by
  induction hf using Submonoid.closure_induction with
  | mem p hp => obtain (⟨r, rfl⟩ | ⟨a, rfl⟩) := hp <;> simp
  | one => simp
  | mul x y _ _ hx hy => simp_all [roots_mul, show x * y ≠ 0 by aesop]

