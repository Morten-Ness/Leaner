import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_centralizer_iff {s : Set A} {z : A} :
    z ∈ NonUnitalStarSubalgebra.centralizer R s ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g := by
  change (∀ g ∈ s ∪ star s, g * z = z * g) ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g
  simp only [Set.mem_union, or_imp, forall_and, and_congr_right_iff]
  exact fun _ =>
    ⟨fun hz a ha => hz _ (Set.star_mem_star.mpr ha), fun hz a ha => star_star a ▸ hz _ ha⟩

