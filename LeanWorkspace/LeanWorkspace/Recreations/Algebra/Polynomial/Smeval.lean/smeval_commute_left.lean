import Mathlib

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [Semiring S]
  [Module R S] [IsScalarTower R S S] [SMulCommClass R S S] {x y : S}

theorem smeval_commute_left (hc : Commute x y) : Commute (p.smeval x) y := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => exact (Polynomial.smeval_add R r s x) ▸ Commute.add_left hr hs
  | monomial n a => simpa [Polynomial.smeval_monomial] using Commute.smul_left (Commute.pow_left hc _) _

