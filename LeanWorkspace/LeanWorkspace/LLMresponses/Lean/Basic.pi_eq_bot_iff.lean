FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

variable {η : Type*} {f : η → Type*}

variable [∀ i, Group (f i)]

theorem pi_eq_bot_iff (H : ∀ i, Subgroup (f i)) : Subgroup.pi Set.univ H = ⊥ ↔ ∀ i, H i = ⊥ := by
  constructor
  · intro h i
    have hle : H i ≤ ⊥ := by
      intro x hx
      have hmem : (fun j => if j = i then cast (by subst j; rfl) x else 1) ∈ Subgroup.pi Set.univ H := by
        intro j hj
        by_cases hji : j = i
        · subst hji
          simpa using hx
        · simp [hji]
      have hbot : (fun j => if j = i then cast (by subst j; rfl) x else 1) ∈ (⊥ : Subgroup ((j : η) => f j)) := by
        simpa [h] using hmem
      have hx1 : x = 1 := by
        have := congrFun (show (fun j => if j = i then cast (by subst j; rfl) x else 1) = 1 from by simpa using hbot) i
        simpa using this
      simpa [hx1]
    exact le_antisymm hle bot_le
  · intro h
    apply le_antisymm
    · intro x hx
      have hx1 : x = 1 := by
        ext i
        have hxi : x i ∈ H i := hx i (by simp)
        have : x i ∈ (⊥ : Subgroup (f i)) := by simpa [h i] using hxi
        simpa using this
      simpa [hx1]
    · exact bot_le
