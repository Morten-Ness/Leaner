import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem map_natDegree_eq_sub {S F : Type*} [Semiring S]
    [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]] {φ : F}
    {p : R[X]} {k : ℕ} (φ_k : ∀ f : R[X], f.natDegree < k → φ f = 0)
    (φ_mon : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = n - k) :
    (φ p).natDegree = p.natDegree - k := Polynomial.mono_map_natDegree_eq k (fun j => j - k) (by simp_all)
    (@fun _ _ h => (tsub_lt_tsub_iff_right h).mpr)
    (φ_k _) φ_mon

