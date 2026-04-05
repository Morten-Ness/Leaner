import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem map_natDegree_eq_natDegree {S F : Type*} [Semiring S]
    [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]]
    {φ : F} (p) (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = n) :
    (φ p).natDegree = p.natDegree := (Polynomial.map_natDegree_eq_sub (fun _ h => (Nat.not_lt_zero _ h).elim) (by simpa)).trans
    p.natDegree.sub_zero

