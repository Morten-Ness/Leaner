import Mathlib

variable {ι α R S : Type*}

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]

theorem isNontrivial_iff_ne_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
    [Nontrivial S] (v : AbsoluteValue R S) :
    v.IsNontrivial ↔ v ≠ .trivial := by
  refine ⟨fun ⟨x, hx₀, hx₁⟩ h ↦ hx₁ <| h.symm ▸ AbsoluteValue.trivial_apply hx₀, fun H ↦ ?_⟩
  simp only [AbsoluteValue.IsNontrivial]
  contrapose! H
  ext1 x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [H, hx]

