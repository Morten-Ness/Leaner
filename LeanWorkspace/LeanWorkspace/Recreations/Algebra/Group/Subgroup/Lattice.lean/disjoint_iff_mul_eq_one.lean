import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem disjoint_iff_mul_eq_one {H₁ H₂ : Subgroup G} :
    Disjoint H₁ H₂ ↔ ∀ {x y : G}, x ∈ H₁ → y ∈ H₂ → x * y = 1 → x = 1 ∧ y = 1 := Subgroup.disjoint_def'.trans
    ⟨fun h x y hx hy hxy =>
      let hx1 : x = 1 := h hx (H₂.inv_mem hy) (eq_inv_iff_mul_eq_one.mpr hxy)
      ⟨hx1, by simpa [hx1] using hxy⟩,
      fun h _ _ hx hy hxy => (h hx (H₂.inv_mem hy) (mul_inv_eq_one.mpr hxy)).1⟩

