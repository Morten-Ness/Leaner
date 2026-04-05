FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conj_mem_conjugatesOfSet {x c : G} :
    x ∈ Group.conjugatesOfSet s → c * x * c⁻¹ ∈ Group.conjugatesOfSet s := by
  intro hx
  rcases hx with ⟨y, hy, hx⟩
  rcases hx with ⟨a, rfl⟩
  refine ⟨y, hy, c * a, ?_⟩
  simp [mul_assoc]
