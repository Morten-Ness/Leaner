import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem isMulCommutative_closure {R} [Ring R] {s : Set R}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    IsMulCommutative (Subring.closure s) := have := Subring.closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

