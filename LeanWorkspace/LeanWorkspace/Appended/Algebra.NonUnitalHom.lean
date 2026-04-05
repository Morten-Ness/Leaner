import Mathlib

section

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

theorem coe_injective : @Function.Injective (A →ₛₙₐ[φ] B) (A → B) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

end

section

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

theorem ext {f g : A →ₛₙₐ[φ] B} (h : ∀ x, f x = g x) : f = g := NonUnitalAlgHom.coe_injective <| funext h

end

section

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

variable {φ' : S →* R} {ψ : S →* T} {χ : R →* T}

variable {B₁ : Type*} [NonUnitalNonAssocSemiring B₁] [DistribMulAction R B₁]

variable [DistribMulAction R B]

variable [DistribMulAction R C]

theorem prod_fst_snd : NonUnitalAlgHom.prod (NonUnitalAlgHom.fst R A B) (NonUnitalAlgHom.snd R A B) = 1 := NonUnitalAlgHom.coe_injective Pi.prod_fst_snd

end

section

variable {R : Type u} {S : Type u₁}

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

theorem restrictScalars_injective :
    Function.Injective (NonUnitalAlgHom.restrictScalars R : (A →ₙₐ[S] B) → A →ₙₐ[R] B) := fun _ _ h ↦ NonUnitalAlgHom.ext (NonUnitalAlgHom.congr_fun h :)

end

section

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

theorem to_distribMulActionHom_injective {f g : A →ₛₙₐ[φ] B}
    (h : (f : A →ₑ+[φ] B) = (g : A →ₑ+[φ] B)) : f = g := by
  ext a
  exact DistribMulActionHom.congr_fun h a

end

section

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

theorem to_mulHom_injective {f g : A →ₛₙₐ[φ] B} (h : (f : A →ₙ* B) = (g : A →ₙ* B)) : f = g := by
  ext a
  exact DFunLike.congr_fun h a

end
