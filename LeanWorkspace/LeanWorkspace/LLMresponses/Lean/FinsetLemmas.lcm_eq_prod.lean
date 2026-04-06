FAIL
import Mathlib

variable {ι α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_eq_prod {s : Finset ι} {f : ι → ℕ} (h : Set.Pairwise s <| Nat.Coprime.onFun f) :
    s.lcm f = s.prod f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.lcm_insert, Finset.prod_insert, ih]
      · refine Nat.Coprime.mul_right ?_
        intro b hb
        exact h (by simp) (by simp [hb])
      · exact ha
      · intro x hx
        intro y hy
        exact h (by simp [hx]) (by simp [hy])
