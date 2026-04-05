import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Field R] {p q : R[X]}

private theorem quotient_mul_add_remainder_eq_aux (p q : R[X]) : q * Polynomial.div p q + Polynomial.mod p q = p := by
  by_cases h : q = 0
  · simp only [h, zero_mul, Polynomial.mod, modByMonic_zero, zero_add]
  · conv =>
      rhs
      rw [← modByMonic_add_div p (q * Polynomial.C q.leadingCoeff⁻¹)]
    rw [Polynomial.div, Polynomial.mod, add_comm, mul_assoc]


private theorem remainder_lt_aux (p : R[X]) (hq : q ≠ 0) : degree (Polynomial.mod p q) < degree q := by
  rw [← degree_mul_leadingCoeff_inv q hq]
  exact degree_modByMonic_lt p (monic_mul_leadingCoeff_inv hq)


theorem rootSet_prod [CommRing S] [IsDomain S] [Algebra R S] {ι : Type*} (f : ι → R[X])
    (s : Finset ι) (h : s.prod f ≠ 0) : (s.prod f).rootSet S = ⋃ i ∈ s, (f i).rootSet S := by
  classical
  simp only [rootSet, aroots, ← Finset.mem_coe]
  rw [Polynomial.map_prod, roots_prod, Finset.bind_toFinset, s.val_toFinset, Finset.coe_biUnion]
  rwa [← Polynomial.map_prod, Ne, Polynomial.map_eq_zero]

