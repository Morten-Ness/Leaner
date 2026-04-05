import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem mono_map_natDegree_eq {S F : Type*} [Semiring S]
    [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]] {φ : F}
    {p : R[X]} (k : ℕ) (fu : ℕ → ℕ) (fu0 : ∀ {n}, n ≤ k → fu n = 0)
    (fc : ∀ {n m}, k ≤ n → n < m → fu n < fu m) (φ_k : ∀ {f : R[X]}, f.natDegree < k → φ f = 0)
    (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = fu n) :
    (φ p).natDegree = fu p.natDegree := by
  refine Polynomial.induction_with_natDegree_le (fun p => (φ p).natDegree = fu p.natDegree)
    p.natDegree (by simp [fu0]) ?_ ?_ _ rfl.le
  · intro n r r0 _
    rw [natDegree_C_mul_X_pow _ _ r0, C_mul_X_pow_eq_monomial, φ_mon_nat _ _ r0]
  · intro f g fg _ fk gk
    rw [natDegree_add_eq_right_of_natDegree_lt fg, map_add]
    by_cases! FG : k ≤ f.natDegree
    · rw [natDegree_add_eq_right_of_natDegree_lt, gk]
      rw [fk, gk]
      exact fc FG fg
    · cases k
      · nomatch FG
      · rwa [φ_k FG, zero_add]

