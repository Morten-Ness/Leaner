import Mathlib

variable {α : Type*}

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

theorem closure_range_of (rels : FreeMonoid α → FreeMonoid α → Prop) :
    Submonoid.closure (Set.range (PresentedMonoid.of rels)) = ⊤ := by
  rw [Submonoid.eq_top_iff']
  intro x
  induction x with | _ a
  induction a with
  | one => exact Submonoid.one_mem _
  | PresentedMonoid.of x => exact subset_closure <| by simp [Set.range, PresentedMonoid.of]
  | mul x y hx hy => exact Submonoid.mul_mem _ hx hy

