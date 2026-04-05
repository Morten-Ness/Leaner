import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {R' α β : Type*}

variable {S' : Type*} [SetLike S' R'] (s : S)

variable [Semiring R']

theorem isMulCommutative_closure {s : Set R'} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    IsMulCommutative (Subsemiring.closure s) := have := Subsemiring.closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

