import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_prod_X_sub_C (s : Finset R) : (s.prod fun a => X - C a).roots = s.val := by
  apply (Polynomial.roots_prod (fun a => X - C a) s ?_).trans
  · simp_rw [Polynomial.roots_X_sub_C]
    rw [Multiset.bind_singleton, Multiset.map_id']
  · refine prod_ne_zero_iff.mpr (fun a _ => X_sub_C_ne_zero a)

