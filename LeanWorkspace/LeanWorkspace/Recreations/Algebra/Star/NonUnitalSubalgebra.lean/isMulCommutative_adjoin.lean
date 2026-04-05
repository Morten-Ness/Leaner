import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem isMulCommutative_adjoin {s : Set A} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (hcomm_star : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a) :
    IsMulCommutative (NonUnitalStarAlgebra.adjoin R s) := by
  have := NonUnitalStarAlgebra.adjoin_le_centralizer_centralizer R s
  refine .of_setLike_mul_comm fun _ h₁ _ h₂ ↦ ?_
  have hcomm : ∀ a ∈ s ∪ star s, ∀ b ∈ s ∪ star s, a * b = b * a := fun a ha b hb ↦
    Set.union_star_self_comm (fun _ ha _ hb ↦ hcomm _ hb _ ha)
      (fun _ ha _ hb ↦ hcomm_star _ hb _ ha) b hb a ha
  apply this at h₁
  apply this at h₂
  rw [← SetLike.mem_coe, NonUnitalStarSubalgebra.coe_centralizer_centralizer] at h₁ h₂
  exact Set.centralizer_centralizer_comm_of_comm hcomm _ h₁ _ h₂

