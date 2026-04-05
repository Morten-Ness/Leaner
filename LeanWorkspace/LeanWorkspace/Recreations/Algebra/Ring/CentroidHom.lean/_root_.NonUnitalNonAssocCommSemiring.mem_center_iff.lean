import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocCommSemiring α]

theorem _root_.NonUnitalNonAssocCommSemiring.mem_center_iff (a : α) :
    a ∈ NonUnitalSubsemiring.center α ↔ ∀ b : α, Commute (L b) (L a) := by
  rw [NonUnitalNonAssocSemiring.mem_center_iff, CentroidHom.centroid_eq_centralizer_mulLeftRight,
    Subsemiring.mem_centralizer_iff, AddMonoid.End.mulRight_eq_mulLeft, Set.union_self]
  aesop

