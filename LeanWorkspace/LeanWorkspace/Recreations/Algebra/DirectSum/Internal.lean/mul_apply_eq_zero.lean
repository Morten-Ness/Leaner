import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedAddMonoid ι] [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R]

variable {A : ι → σ} [SetLike.GradedMonoid A]

theorem mul_apply_eq_zero {r r' : ⨁ i, A i} {m n : ι}
    (hr : ∀ i < m, r i = 0) (hr' : ∀ i < n, r' i = 0) ⦃k : ι⦄ (hk : k < m + n) :
    (r * r') k = 0 := by
  classical
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero, DirectSum.coe_mul_apply]
  apply Finset.sum_eq_zero fun x hx ↦ ?_
  obtain (hx | hx) : x.1 < m ∨ x.2 < n := by
    by_contra! ⟨hm, hn⟩
    obtain rfl : x.1 + x.2 = k := by simp_all
    apply lt_irrefl (m + n) <| lt_of_le_of_lt (by gcongr) hk
  all_goals simp [hr, hr', hx]

