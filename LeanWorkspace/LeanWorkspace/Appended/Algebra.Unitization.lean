import Mathlib

section

variable {S R A : Type*} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type*} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type*} [Semiring C] [Algebra R C]

theorem algHom_ext'' {F : Type*}
    [FunLike F (Unitization R A) C] [AlgHomClass F R (Unitization R A) C] {φ ψ : F}
    (h : ∀ a : A, φ a = ψ a) : φ = ψ := Unitization.algHom_ext h (fun r => by simp only [AlgHomClass.commutes])

end

section

variable {S R A : Type*} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type*} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type*} [Semiring C] [Algebra R C]

theorem algHom_ext' {φ ψ : Unitization R A →ₐ[R] C}
    (h :
      φ.toNonUnitalAlgHom.comp (Unitization.inrNonUnitalAlgHom R A) =
        ψ.toNonUnitalAlgHom.comp (Unitization.inrNonUnitalAlgHom R A)) :
    φ = ψ := Unitization.algHom_ext'' (NonUnitalAlgHom.congr_fun h)

end

section

variable {S R A : Type*} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type*} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type*} [Semiring C] [Algebra R C]

theorem algHom_ext {F : Type*}
    [FunLike F (Unitization R A) B] [AlgHomClass F S (Unitization R A) B] {φ ψ : F}
    (h : ∀ a : A, φ a = ψ a)
    (h' : ∀ r, φ (algebraMap R (Unitization R A) r) = ψ (algebraMap R (Unitization R A) r)) :
    φ = ψ := by
  refine DFunLike.ext φ ψ (fun x ↦ ?_)
  induction x
  simp only [map_add, ← Unitization.algebraMap_eq_inl, h, h']

end

section

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A → Prop}
    (inl_add_inr : ∀ (r : R) (a : A), P (Unitization.inl r + (a : Unitization R A))) (x) : P x := Unitization.inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.fst x.snd

end

section

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inl_add [Add R] [AddZeroClass A] (r₁ r₂ : R) :
    (Unitization.inl (r₁ + r₂) : Unitization R A) = Unitization.inl r₁ + Unitization.inl r₂ := Unitization.ext rfl (add_zero 0).symm

end

section

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass A] (x : Unitization R A) :
    Unitization.inl x.fst + (x.snd : Unitization R A) = x := Unitization.ext (add_zero x.fst) (zero_add x.snd)

end

section

variable {R A : Type*}

theorem inl_mul_inr [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : ((Unitization.inl r : Unitization R A) * a) = ↑(r • a) := Unitization.ext (mul_zero r) <| by simp

end

section

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inl_smul [Zero A] [SMul S R] [SMulZeroClass S A] (s : S) (r : R) :
    (Unitization.inl (s • r) : Unitization R A) = s • Unitization.inl r := Unitization.ext rfl (smul_zero s).symm

end

section

variable {R A : Type*}

theorem inl_star [Star R] [AddMonoid A] [StarAddMonoid A] (r : R) :
    Unitization.inl (star r) = star (Unitization.inl r : Unitization R A) := Unitization.ext rfl (by simp only [Unitization.snd_star, star_zero, Unitization.snd_inl])

end

section

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inl_sub [AddGroup R] [AddGroup A] (r₁ r₂ : R) :
    (Unitization.inl (r₁ - r₂) : Unitization R A) = Unitization.inl r₁ - Unitization.inl r₂ := Unitization.ext rfl (sub_zero 0).symm

end

section

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂ := Unitization.ext (add_zero 0).symm rfl

end

section

variable {R A : Type*}

theorem inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A) :
    (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂ := Unitization.ext (mul_zero _).symm <| by simp

end

section

variable {R A : Type*}

theorem inr_mul_inl [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : a * (Unitization.inl r : Unitization R A) = ↑(r • a) := Unitization.ext (zero_mul r) <| by simp

end

section

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (r : S) (m : A) :
    (↑(r • m) : Unitization R A) = r • (m : Unitization R A) := Unitization.ext (smul_zero _).symm rfl

end

section

variable {R A : Type*}

theorem inr_star [AddMonoid R] [StarAddMonoid R] [Star A] (a : A) :
    ↑(star a) = star (a : Unitization R A) := Unitization.ext (by simp only [Unitization.fst_star, star_zero, Unitization.fst_inr]) rfl

end

section

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inr_sub [AddGroup R] [AddGroup A] (m₁ m₂ : A) : (↑(m₁ - m₂) : Unitization R A) = m₁ - m₂ := Unitization.ext (sub_zero 0).symm rfl

end

section

theorem isIdempotentElem_inr_iff (R : Type*) {A : Type*} [MulZeroClass R]
    [AddZeroClass A] [Mul A] [SMulWithZero R A] {a : A} :
    IsIdempotentElem (a : Unitization R A) ↔ IsIdempotentElem a := by
  simp only [IsIdempotentElem, ← Unitization.inr_mul, Unitization.inr_injective.eq_iff]

alias ⟨_, IsIdempotentElem.inr⟩ := isIdempotentElem_inr_iff

end

section

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem linearMap_ext {N} [CommSemiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
    [Module S R] [Module S A] [Module S N] ⦃f g : Unitization R A →ₗ[S] N⦄
    (hl : ∀ r, f (Unitization.inl r) = g (Unitization.inl r)) (hr : ∀ a : A, f a = g a) : f = g := (Unitization.linearEquiv S R A).arrowCongr (.refl ..) |>.injective <|
    LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

end

section

variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]

variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

variable [Semiring C] [Algebra R C] [StarRing C]

theorem starAlgHom_ext {φ ψ : Unitization R A →⋆ₐ[R] C}
    (h : (φ : Unitization R A →⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A) =
      (ψ : Unitization R A →⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A)) :
    φ = ψ := Unitization.algHom_ext'' <| DFunLike.congr_fun h

end

section

variable {R A B C : Type*} [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

variable [NonUnitalSemiring C] [StarRing C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]

variable [StarModule R B] [StarModule R C]

theorem starMap_injective {φ : A →⋆ₙₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (Unitization.starMap φ) := by
  intro x y h
  ext
  · simpa using congr($(h).fst)
  · exact hφ <| by simpa [Unitization.algebraMap_eq_inl] using congr($(h).snd)

end

section

variable {R A B C : Type*} [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

variable [NonUnitalSemiring C] [StarRing C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]

variable [StarModule R B] [StarModule R C]

theorem starMap_surjective {φ : A →⋆ₙₐ[R] B} (hφ : Function.Surjective φ) :
    Function.Surjective (Unitization.starMap φ) := by
  intro x
  induction x using Unitization.ind with
  | inl_add_inr r b =>
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨Unitization.mk (r, a), by rfl⟩

end
