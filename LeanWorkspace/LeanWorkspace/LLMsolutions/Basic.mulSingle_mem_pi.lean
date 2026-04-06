import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

variable {η : Type*} {f : η → Type*}

variable [∀ i, Group (f i)]

theorem mulSingle_mem_pi [DecidableEq η] {I : Set η} {H : ∀ i, Subgroup (f i)} (i : η) (x : f i) :
    Pi.mulSingle i x ∈ Subgroup.pi I H ↔ i ∈ I → x ∈ H i := by
  constructor
  · intro hx hi
    simpa [Pi.mulSingle] using hx i hi
  · intro hx j hj
    by_cases hji : j = i
    · subst hji
      simpa [Pi.mulSingle] using hx hj
    · simp [Pi.mulSingle, hji]
