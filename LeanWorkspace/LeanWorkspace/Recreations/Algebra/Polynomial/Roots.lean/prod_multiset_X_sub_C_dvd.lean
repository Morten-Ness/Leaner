import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem prod_multiset_X_sub_C_dvd (p : R[X]) : (p.roots.map fun a => X - C a).prod ∣ p := by
  classical
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R)
    (Polynomial.monic_multisetProd_X_sub_C p.roots)]
  rw [Polynomial.prod_multiset_root_eq_finset_root, Polynomial.map_prod]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ h => ?_) fun a _ => ?_
  · simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
    exact (pairwise_coprime_X_sub_C (IsFractionRing.injective R <| FractionRing R) h).pow
  · exact Polynomial.map_dvd _ (pow_rootMultiplicity_dvd p a)

