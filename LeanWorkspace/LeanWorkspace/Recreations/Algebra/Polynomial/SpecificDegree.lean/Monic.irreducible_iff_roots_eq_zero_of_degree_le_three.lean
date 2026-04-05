import Mathlib

variable {R : Type*} [CommRing R] [IsDomain R]

theorem Monic.irreducible_iff_roots_eq_zero_of_degree_le_three {p : R[X]} (hp : p.Monic)
    (hp2 : 2 ≤ p.natDegree) (hp3 : p.natDegree ≤ 3) : Irreducible p ↔ p.roots = 0 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : p ≠ 1 := by rintro rfl; rw [natDegree_one] at hp2; cases hp2
  rw [hp.irreducible_iff_lt_natDegree_lt hp1]
  simp_rw [show p.natDegree / 2 = 1 from
      (Nat.div_le_div_right hp3).antisymm
        (by apply Nat.div_le_div_right (c := 2) hp2),
    show Finset.Ioc 0 1 = {1} from rfl,
    Finset.mem_singleton, Multiset.eq_zero_iff_forall_notMem, mem_roots hp0, ← dvd_iff_isRoot]
  refine ⟨fun h r ↦ h _ (monic_X_sub_C r) (natDegree_X_sub_C r), fun h q hq hq1 ↦ ?_⟩
  rw [hq.eq_X_add_C hq1, ← sub_neg_eq_add, ← C_neg]
  apply h

