import Mathlib

variable {R A : Type*}

theorem isSelfAdjoint_smul_of_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A]
    [StarAddMonoid R] [StarAddMonoid A] [StarModule R A] {r : R} (hr : r ∈ skewAdjoint R) {a : A}
    (ha : a ∈ skewAdjoint A) : IsSelfAdjoint (r • a) := (star_smul _ _).trans <| (congr_arg₂ _ hr ha).trans <| neg_smul_neg _ _

protected instance IsStarNormal.zero [NonUnitalNonAssocSemiring R]
    [StarAddMonoid R] : IsStarNormal (0 : R) :=
  ⟨by simp only [Commute.refl, star_zero]⟩

protected instance IsStarNormal.one [MulOneClass R] [StarMul R] : IsStarNormal (1 : R) :=
  ⟨by simp only [Commute.refl, star_one]⟩

protected instance IsStarNormal.star [Mul R] [StarMul R] {x : R} [IsStarNormal x] :
    IsStarNormal (star x) :=
  ⟨show star (star x) * star x = star x * star (star x) by rw [star_star, star_comm_self']⟩

protected instance IsStarNormal.neg [NonUnitalNonAssocRing R]
    [StarAddMonoid R] {x : R} [IsStarNormal x] : IsStarNormal (-x) :=
  ⟨show star (-x) * -x = -x * star (-x) by simp_rw [star_neg, neg_mul_neg, star_comm_self']⟩

protected instance IsStarNormal.val_inv [Monoid R] [StarMul R] {x : Rˣ} [IsStarNormal (x : R)] :
    IsStarNormal (↑x⁻¹ : R) where
  star_comm_self := by simpa [← Units.coe_star_inv, -Commute.units_val_iff] using star_comm_self

protected instance IsStarNormal.map {F R S : Type*} [Mul R] [Star R] [Mul S] [Star S]
    [FunLike F R S] [MulHomClass F R S] [StarHomClass F R S] (f : F) (r : R) [hr : IsStarNormal r] :
    IsStarNormal (f r) where
  star_comm_self := by simpa [map_star] using congr(f $(hr.star_comm_self))

protected instance IsStarNormal.smul {R A : Type*} [SMul R A] [Star R] [Star A] [Mul A]
    [StarModule R A] [SMulCommClass R A A] [IsScalarTower R A A]
    (r : R) (a : A) [ha : IsStarNormal a] : IsStarNormal (r • a) where
  star_comm_self := star_smul r a ▸ ha.star_comm_self.smul_left (star r) |>.smul_right r

-- see Note [lower instance priority]

