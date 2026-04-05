import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_map_eq (H : Subgroup G) : comap f (map f H) = H ⊔ f.ker := by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (Subgroup.ker_le_comap _ _))
  intro x hx; simp only [mem_map, mem_comap] at hx
  rcases hx with ⟨y, hy, hy'⟩
  rw [← mul_inv_cancel_left y x]
  exact mul_mem_sup hy (by simp [MonoidHom.mem_ker, hy'])

