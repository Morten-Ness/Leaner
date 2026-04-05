import Mathlib

section

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem cancel_left {g₁ g₂ : A →ₐ[R] B} {f : B →ₐ[R] C} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ := ⟨fun h => AlgHom.ext <| fun _ ↦ hf.eq_iff.mp <| AlgHom.ext_iff.mp h _, fun h => h ▸ rfl⟩

end

section

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem cancel_right {g₁ g₂ : B →ₐ[R] C} {f : A →ₐ[R] B} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := ⟨fun h => AlgHom.ext <| hf.forall.2 (AlgHom.ext_iff.1 h), fun h => h ▸ rfl⟩

end

section

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+ B) := RingHom.coe_addMonoidHom_injective.comp AlgHom.coe_ringHom_injective

end

section

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem coe_monoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →* B) := RingHom.coe_monoidHom_injective.comp AlgHom.coe_ringHom_injective

end

section

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem coe_ringHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+* B) := fun φ₁ φ₂ H =>
  AlgHom.coe_fn_injective <| show ((φ₁ : A →+* B) : A → B) = ((φ₂ : A →+* B) : A → B) from congr_arg _ H

end

section

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

theorem coe_ringHom_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₐ[R] B) : A →+* B) = f := rfl

-- make the coercion the simp-normal form

end

section

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x := φ.toLinearMap.map_smul_of_tower r x

end

section

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

theorem toAlgHom_injective [FaithfulSMul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) := fun _m₁ _m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r

end

section

variable {R S : Type*}

theorem toIntAlgHom_injective [Ring R] [Ring S] :
    Function.Injective (RingHom.toIntAlgHom : (R →+* S) → _) := fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun e x)

end

section

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem toLinearMap_injective :
    Function.Injective (AlgHom.toLinearMap : _ → A →ₗ[R] B) := fun _φ₁ _φ₂ h =>
  AlgHom.ext <| LinearMap.congr_fun h

end
