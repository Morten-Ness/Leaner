import Mathlib

open scoped TensorProduct

variable (R A L M : Type*)

variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [CommRing A] [Algebra R A]

variable (N : LieSubmodule R L M)

set_option backward.privateInPublic true in
private def bracket' : A ⊗[R] L →ₗ[A] A ⊗[R] M →ₗ[A] A ⊗[R] M := TensorProduct.curry <|
    TensorProduct.AlgebraTensorModule.map
        (LinearMap.mul' A A) (LieModule.toModuleHom R L M : L ⊗[R] M →ₗ[R] M) ∘ₗ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A A L A M).toLinearMap


private theorem bracket'_tmul (s t : A) (x : L) (m : M) :
    bracket' R A L M (s ⊗ₜ[R] x) (t ⊗ₜ[R] m) = (s * t) ⊗ₜ ⁅x, m⁆ := rfl


set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
private theorem bracket_def (x : A ⊗[R] L) (m : A ⊗[R] M) : ⁅x, m⁆ = bracket' R A L M x m := rfl


set_option backward.privateInPublic true in
private theorem bracket_lie_self (x : A ⊗[R] L) : ⁅x, x⁆ = 0 := by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero]
  · intro a l
    simp only [bracket'_tmul, TensorProduct.tmul_zero, lie_self]
  · intro z₁ z₂ h₁ h₂
    suffices bracket' R A L L z₁ z₂ + bracket' R A L L z₂ z₁ = 0 by
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂,
        zero_add, add_zero, add_comm, this]
    refine z₁.induction_on ?_ ?_ ?_
    · simp only [map_zero, add_zero, LinearMap.zero_apply]
    · intro a₁ l₁; refine z₂.induction_on ?_ ?_ ?_
      · simp only [map_zero, add_zero, LinearMap.zero_apply]
      · intro a₂ l₂
        simp only [← lie_skew l₂ l₁, mul_comm a₁ a₂, TensorProduct.tmul_neg, bracket'_tmul,
          add_neg_cancel]
      · intro y₁ y₂ hy₁ hy₂
        simp only [hy₁, hy₂, add_add_add_comm, add_zero, LinearMap.add_apply, map_add]
    · intro y₁ y₂ hy₁ hy₂
      simp only [add_add_add_comm, hy₁, hy₂, add_zero, LinearMap.add_apply, map_add]


set_option backward.privateInPublic true in
private theorem bracket_leibniz_lie (x y : A ⊗[R] L) (z : A ⊗[R] M) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero, add_zero, LinearMap.zero_apply]
  · intro a₁ l₁
    refine y.induction_on ?_ ?_ ?_
    · simp only [map_zero, add_zero, LinearMap.zero_apply]
    · intro a₂ l₂
      refine z.induction_on ?_ ?_ ?_
      · simp only [map_zero, add_zero]
      · intro a₃ l₃; simp only [bracket'_tmul]
        rw [mul_left_comm a₂ a₁ a₃, mul_assoc, leibniz_lie, TensorProduct.tmul_add]
      · grind
    · grind [LinearMap.add_apply]
  · grind [LinearMap.add_apply]


theorem lie_baseChange {I : LieIdeal R L} {N : LieSubmodule R L M} :
    ⁅I, N⁆.baseChange A = ⁅I.baseChange A, N.baseChange A⁆ := by
  set s : Set (A ⊗[R] M) := { m | ∃ x ∈ I, ∃ n ∈ N, 1 ⊗ₜ ⁅x, n⁆ = m}
  have : (TensorProduct.mk R A M 1) '' {m | ∃ x ∈ I, ∃ n ∈ N, ⁅x, n⁆ = m} = s := by ext; simp [s]
  rw [← toSubmodule_inj, LieSubmodule.coe_baseChange, lieIdeal_oper_eq_linear_span',
    Submodule.baseChange_span, this, lieIdeal_oper_eq_linear_span']
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.mpr ?_)
  · rintro - ⟨x, hx, m, hm, rfl⟩
    exact ⟨1 ⊗ₜ x, LieSubmodule.tmul_mem_baseChange_of_mem 1 hx,
           1 ⊗ₜ m, LieSubmodule.tmul_mem_baseChange_of_mem 1 hm, by simp⟩
  · rintro - ⟨x, hx, m, hm, rfl⟩
    rw [LieSubmodule.mem_baseChange_iff] at hx hm
    refine Submodule.span_induction₂ (p := fun x m _ _ ↦ ⁅x, m⁆ ∈ Submodule.span A s)
      ?_ (by simp) (by simp) ?_ ?_ ?_ ?_ hx hm
    · rintro - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact Submodule.subset_span ⟨x, hx, y, hy, by simp⟩
    all_goals { intros; simp [add_mem, Submodule.smul_mem, *] }

