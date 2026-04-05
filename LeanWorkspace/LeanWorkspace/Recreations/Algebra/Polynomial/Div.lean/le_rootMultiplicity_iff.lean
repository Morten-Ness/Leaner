import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem le_rootMultiplicity_iff (p0 : p ≠ 0) {a : R} {n : ℕ} :
    n ≤ Polynomial.rootMultiplicity a p ↔ (Polynomial.X - Polynomial.C a) ^ n ∣ p := by
  classical
  simp_rw [Polynomial.rootMultiplicity, dif_neg p0, Nat.le_find_iff, not_not]
  refine ⟨fun h => ?_, fun h m hm => (pow_dvd_pow _ hm).trans h⟩
  rcases n with - | n
  · rw [pow_zero]
    apply one_dvd
  · exact h n n.lt_succ_self

