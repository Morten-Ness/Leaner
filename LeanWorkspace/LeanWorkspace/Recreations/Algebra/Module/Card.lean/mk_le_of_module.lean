import Mathlib

theorem mk_le_of_module (R : Type u) (E : Type v)
    [AddCommGroup E] [Ring R] [IsDomain R] [Module R E] [Nontrivial E] [Module.IsTorsionFree R E] :
    Cardinal.lift.{v} (#R) ≤ Cardinal.lift.{u} (#E) := by
  obtain ⟨x, hx⟩ : ∃ (x : E), x ≠ 0 := exists_ne 0
  have : Function.Injective (fun k ↦ k • x) := smul_left_injective R hx
  exact lift_mk_le_lift_mk_of_injective this

