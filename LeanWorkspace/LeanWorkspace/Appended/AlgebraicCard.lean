import Mathlib

section

theorem aleph0_le_cardinalMk_of_charZero (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] [CharZero A] : ℵ₀ ≤ #{ x : A // IsAlgebraic R x } := infinite_iff.1 (Set.infinite_coe_iff.2 <| Algebraic.infinite_of_charZero R A)

end

section

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

theorem cardinalMk_le_max : #{ x : A // IsAlgebraic R x } ≤ max #R ℵ₀ := by
  rw [← lift_id #_, ← lift_id #R]
  exact Algebraic.cardinalMk_lift_le_max R A

end

section

open scoped Polynomial

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

theorem cardinalMk_le_mul : #{ x : A // IsAlgebraic R x } ≤ #R[X] * ℵ₀ := by
  rw [← lift_id #_, ← lift_id #R[X]]
  exact Algebraic.cardinalMk_lift_le_mul R A

end

section

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

theorem cardinalMk_lift_le_max :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ max (Cardinal.lift.{v} #R) ℵ₀ := (Algebraic.cardinalMk_lift_le_mul R A).trans <| by grw [lift_le.2 cardinalMk_le_max]; simp

end

section

open scoped Polynomial

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

theorem cardinalMk_lift_le_mul :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ Cardinal.lift.{v} #R[X] * ℵ₀ := by
  rw [← mk_uLift, ← mk_uLift]
  choose g hg₁ hg₂ using fun x : { x : A | IsAlgebraic R x } => x.coe_prop
  refine lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le g fun f => ?_
  rw [lift_le_aleph0, le_aleph0_iff_set_countable]
  suffices MapsTo (↑) (g ⁻¹' {f}) (f.rootSet A) from
    this.countable_of_injOn Subtype.coe_injective.injOn (f.rootSet_finite A).countable
  rintro x (rfl : g x = f)
  exact mem_rootSet.2 ⟨hg₁ x, hg₂ x⟩

end

section

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

theorem cardinalMk_lift_of_infinite [Infinite R] :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } = Cardinal.lift.{v} #R := ((Algebraic.cardinalMk_lift_le_max R A).trans_eq (max_eq_left <| aleph0_le_mk _)).antisymm <|
    lift_mk_le'.2 ⟨⟨fun x => ⟨algebraMap R A x, isAlgebraic_algebraMap _⟩, fun _ _ h =>
      FaithfulSMul.algebraMap_injective R A (Subtype.ext_iff.1 h)⟩⟩

end

section

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

variable [Countable R]

theorem cardinalMk_of_countable_of_charZero [CharZero A] :
    #{ x : A // IsAlgebraic R x } = ℵ₀ := (Algebraic.countable R A).le_aleph0.antisymm (Algebraic.aleph0_le_cardinalMk_of_charZero R A)

end

section

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

theorem cardinalMk_of_infinite [Infinite R] : #{ x : A // IsAlgebraic R x } = #R := lift_inj.1 <| Algebraic.cardinalMk_lift_of_infinite R A

end

section

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

variable [Countable R]

theorem countable : Set.Countable { x : A | IsAlgebraic R x } := by
  rw [← le_aleph0_iff_set_countable, ← lift_le_aleph0]
  apply (Algebraic.cardinalMk_lift_le_max R A).trans
  simp

end

section

theorem infinite_of_charZero (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    [CharZero A] : { x : A | IsAlgebraic R x }.Infinite := by
  letI := MulActionWithZero.nontrivial R A
  exact infinite_of_injective_forall_mem Nat.cast_injective isAlgebraic_nat

end
