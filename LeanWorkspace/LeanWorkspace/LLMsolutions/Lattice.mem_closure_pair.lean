FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem mem_closure_pair {x y z : C} :
    z ∈ Subgroup.closure ({x, y} : Set C) ↔ ∃ m n : ℤ, x ^ m * y ^ n = z := by
  constructor
  · intro hz
    let S : Subgroup C :=
      { carrier := {z : C | ∃ m n : ℤ, x ^ m * y ^ n = z}
        , one_mem' := by
            exact ⟨0, 0, by simp⟩
        , mul_mem' := by
            intro a b ha hb
            rcases ha with ⟨m₁, n₁, rfl⟩
            rcases hb with ⟨m₂, n₂, rfl⟩
            refine ⟨m₁ + m₂, n₁ + n₂, ?_⟩
            calc
              x ^ (m₁ + m₂) * y ^ (n₁ + n₂)
                  = (x ^ m₁ * x ^ m₂) * (y ^ n₁ * y ^ n₂) := by
                      simp [zpow_add₀]
              _ = x ^ m₁ * (x ^ m₂ * (y ^ n₁ * y ^ n₂)) := by
                      ac_rfl
        , inv_mem' := by
            intro a ha
            rcases ha with ⟨m, n, rfl⟩
            refine ⟨-m, -n, ?_⟩
            simp [mul_comm] }
    have hx : x ∈ S := by
      exact ⟨1, 0, by simp⟩
    have hy : y ∈ S := by
      exact ⟨0, 1, by simp [mul_comm]⟩
    have hsubset : ({x, y} : Set C) ⊆ S := by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact hx
      · exact hy
    have hcl : Subgroup.closure ({x, y} : Set C) ≤ S := by
      rw [Subgroup.closure_le]
      exact hsubset
    exact hcl hz
  · rintro ⟨m, n, rfl⟩
    have hx : x ∈ Subgroup.closure ({x, y} : Set C) :=
      Subgroup.subset_closure (by simp)
    have hy : y ∈ Subgroup.closure ({x, y} : Set C) :=
      Subgroup.subset_closure (by simp)
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hx m) (Subgroup.zpow_mem _ hy n)
