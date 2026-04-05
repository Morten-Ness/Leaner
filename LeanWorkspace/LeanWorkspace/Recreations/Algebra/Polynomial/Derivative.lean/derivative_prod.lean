import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem derivative_prod [DecidableEq ι] {s : Multiset ι} {f : ι → R[X]} :
    Polynomial.derivative (Multiset.map f s).prod =
      (Multiset.map (fun i => (Multiset.map f (s.erase i)).prod * Polynomial.derivative (f i)) s).sum := by
  refine Multiset.induction_on s (by simp) fun i s h => ?_
  rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.derivative_mul, Multiset.map_cons _ i s,
    Multiset.sum_cons, Multiset.erase_cons_head, mul_comm (Polynomial.derivative (f i))]
  congr
  rw [h, ← AddMonoidHom.coe_mulLeft, (AddMonoidHom.mulLeft (f i)).map_multiset_sum _,
    AddMonoidHom.coe_mulLeft]
  simp only [Function.comp_apply, Multiset.map_map]
  refine congr_arg _ (Multiset.map_congr rfl fun j hj => ?_)
  rw [← mul_assoc, ← Multiset.prod_cons, ← Multiset.map_cons]
  by_cases hij : i = j
  · simp [hij, Multiset.cons_erase hj]
  · simp [hij]

