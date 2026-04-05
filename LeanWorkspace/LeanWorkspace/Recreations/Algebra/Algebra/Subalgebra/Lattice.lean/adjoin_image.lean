import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_image (f : A →ₐ[R] B) (s : Set A) : Algebra.adjoin R (f '' s) = (Algebra.adjoin R s).map f := le_antisymm (Algebra.adjoin_le <| Set.image_mono Algebra.subset_adjoin) <|
    Subalgebra.map_le.2 <| Algebra.adjoin_le <| Set.image_subset_iff.1 <| by
      simp only [Set.image_id', coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
        Subalgebra.coe_comap]
      exact fun x hx => Algebra.subset_adjoin ⟨x, hx, rfl⟩

