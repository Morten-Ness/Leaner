FAIL
import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem smul_mem_of_mem_closure_of_mem {X : Type*} [MulAction G X] {s : Set G} {t : Set X}
    (hs : ∀ g ∈ s, g⁻¹ ∈ s) (hst : ∀ᵉ (g ∈ s) (x ∈ t), g • x ∈ t) {g : G}
    (hg : g ∈ Subgroup.closure s) {x : X} (hx : x ∈ t) : g • x ∈ t := by
  let H : Subgroup G :=
    { carrier := {g : G | ∀ x ∈ t, g • x ∈ t}
      one_mem' := by
        show ∀ x ∈ t, (1 : G) • x ∈ t
        intro x hx
        simpa using hx
      mul_mem' := by
        intro a b ha hb
        show ∀ x ∈ t, (a * b) • x ∈ t
        intro x hx
        simpa [smul_smul] using ha (b • x) (hb x hx)
      inv_mem' := by
        intro a ha
        show ∀ x ∈ t, a⁻¹ • x ∈ t
        intro x hx
        have h1 : a • (a⁻¹ • x) ∈ t := ha x hx
        simpa [smul_smul] using h1 }
  have hs_subset : s ⊆ H := by
    intro g hgS
    show ∀ x ∈ t, g • x ∈ t
    intro x hx
    exact hst g hgS x hx
  have hclosure : Subgroup.closure s ≤ H := by
    rw [Subgroup.closure_le]
    exact hs_subset
  exact hclosure hg x hx
