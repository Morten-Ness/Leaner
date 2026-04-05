import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

variable {p q : R[A]}

variable [AddZeroClass A]

variable [Add B]

theorem apply_add_of_supDegree_le (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftStrictMono B] [AddRightStrictMono B]
    (hD : D.Injective) {ap aq : A} (hp : p.supDegree D ≤ D ap) (hq : q.supDegree D ≤ D aq) :
    (p * q) (ap + aq) = p ap * q aq := by
  classical
  simp_rw [mul_apply, Finsupp.sum]
  rw [Finset.sum_eq_single ap, Finset.sum_eq_single aq, if_pos rfl]
  · refine fun a ha hne => if_neg (fun he => ?_)
    apply_fun D at he; simp_rw [hadd] at he
    exact (add_lt_add_right (((Finset.le_sup ha).trans hq).lt_of_ne <| hD.ne_iff.2 hne) _).ne he
  · intro h; rw [if_pos rfl, Finsupp.notMem_support_iff.1 h, mul_zero]
  · refine fun a ha hne => Finset.sum_eq_zero (fun a' ha' => if_neg <| fun he => ?_)
    apply_fun D at he
    simp_rw [hadd] at he
    have := addLeftMono_of_addLeftStrictMono B
    exact (add_lt_add_of_lt_of_le (((Finset.le_sup ha).trans hp).lt_of_ne <| hD.ne_iff.2 hne)
      <| (Finset.le_sup ha').trans hq).ne he
  · refine fun h => Finset.sum_eq_zero (fun a _ => ite_eq_right_iff.mpr <| fun _ => ?_)
    rw [Finsupp.notMem_support_iff.mp h, zero_mul]

