FAIL
import Mathlib

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

theorem hasFiniteMulSupport_fun_pow_count (s : Multiset α) (f : α → M) :
    (fun a ↦ (f a) ^ s.count a).HasFiniteMulSupport := by
  classical
  simpa [DFunLike.hasFiniteSupport_iff_eventuallyEq] using
    (s.toFinset.finite_toSet.eventuallyEq fun a ha => by
      have hcount : s.count a = 0 := Multiset.count_eq_zero_of_not_mem ha
      simp [hcount])
