import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_eq_span (s : Set A) : (NonUnitalAlgebra.adjoin R s).toSubmodule = span R (Subsemigroup.closure s) := by
  apply le_antisymm
  · intro x hx
    induction hx using NonUnitalAlgebra.adjoin_induction with
    | mem x hx => exact subset_span <| Subsemigroup.subset_closure hx
    | add x y _ _ hpx hpy => exact add_mem hpx hpy
    | zero => exact zero_mem _
    | mul x y _ _ hpx hpy =>
      apply span_induction₂ ?Hs (by simp) (by simp) ?Hadd_l ?Hadd_r ?Hsmul_l ?Hsmul_r hpx hpy
      case Hs => exact fun x y hx hy ↦ subset_span <| mul_mem hx hy
      case Hadd_l => exact fun x y z _ _ _ hxz hyz ↦ by simpa [add_mul] using add_mem hxz hyz
      case Hadd_r => exact fun x y z _ _ _ hxz hyz ↦ by simpa [mul_add] using add_mem hxz hyz
      case Hsmul_l => exact fun r x y _ _ hxy ↦ by simpa [smul_mul_assoc] using smul_mem _ _ hxy
      case Hsmul_r => exact fun r x y _ _ hxy ↦ by simpa [mul_smul_comm] using smul_mem _ _ hxy
    | smul r x _ hpx => exact smul_mem _ _ hpx
  · apply span_le.2 _
    change Subsemigroup.closure s ≤ (NonUnitalAlgebra.adjoin R s).toSubsemigroup
    exact Subsemigroup.closure_le.2 (NonUnitalAlgebra.subset_adjoin R)

