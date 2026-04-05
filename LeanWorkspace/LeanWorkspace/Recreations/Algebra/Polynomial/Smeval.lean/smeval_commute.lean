import Mathlib

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [Semiring S]
  [Module R S] [IsScalarTower R S S] [SMulCommClass R S S] {x y : S}

theorem smeval_commute (hc : Commute x y) : Commute (p.smeval x) (q.smeval y) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => exact (Polynomial.smeval_add R r s x) ▸ Commute.add_left hr hs
  | monomial n a =>
    simp only [Polynomial.smeval_monomial]
    refine Commute.smul_left ?_ a
    induction n with
    | zero => simp only [npow_zero, Commute.one_left]
    | succ n ih =>
      refine (commute_iff_eq (x ^ (n + 1)) (q.smeval y)).mpr ?_
      rw [commute_iff_eq (x ^ n) (q.smeval y)] at ih
      have hxq : x * q.smeval y = q.smeval y * x := by
        refine (commute_iff_eq x (q.smeval y)).mp ?_
        exact Commute.symm (Polynomial.smeval_commute_left R q (Commute.symm hc))
      rw [pow_succ, ← mul_assoc, ← ih, mul_assoc, hxq, mul_assoc]

