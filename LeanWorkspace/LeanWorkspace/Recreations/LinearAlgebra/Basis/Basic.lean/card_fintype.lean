import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

theorem card_fintype [Semiring R] [AddCommMonoid M] [Module R M] [Fintype ι] (b : Basis ι R M)
    [Fintype R] [Fintype M] :
    card M = card R ^ card ι := by
  classical
    calc
      card M = card (ι → R) := card_congr b.equivFun.toEquiv
      _ = card R ^ card ι := by simp

