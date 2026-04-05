import Mathlib

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem forall_zpowers {x : G} {p : Subgroup.zpowers x → Prop} : (∀ g, p g) ↔ ∀ m : ℤ, p ⟨x ^ m, m, rfl⟩ := Set.forall_subtype_range_iff

-- increasing simp priority. Better lemma than `Subtype.exists`

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem npow_mem_zpowers (g : G) (k : ℕ) : g ^ k ∈ Subgroup.zpowers g := zpow_natCast g k ▸ Subgroup.zpow_mem_zpowers g k

-- increasing simp priority. Better lemma than `Subtype.exists`

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem zpow_mem_zpowers (g : G) (k : ℤ) : g ^ k ∈ Subgroup.zpowers g := Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {s : Set G} {g : G}

theorem zpowers_inv : Subgroup.zpowers g⁻¹ = Subgroup.zpowers g := eq_of_forall_ge_iff fun _ ↦ by simp only [Subgroup.zpowers_le, inv_mem_iff]

end
