import Mathlib

open scoped Pointwise

variable {M : Type*}

variable [ConditionallyCompleteLattice M]

variable [Group M] [MulLeftMono M] [MulRightMono M]
  {s t : Set M}

theorem csSup_mul (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sSup (s * t) = sSup s * sSup t := csSup_image2_eq_csSup_csSup (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs₀ hs₁ ht₀ ht₁

