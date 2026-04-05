import Mathlib

variable {S R : Type*} [Ring R] [SetLike S R] (C : S)

theorem IsOrderedRing.mkOfCone [RingConeClass S R] :
    letI _ : PartialOrder R := .mkOfAddGroupCone C
    IsOrderedRing R :=
  letI _ : PartialOrder R := .mkOfAddGroupCone C
  haveI : IsOrderedAddMonoid R := .mkOfCone C
  haveI : ZeroLEOneClass R := ⟨show _ ∈ C by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ C by simpa using mul_mem xnn ynn

