FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Normal.of_map_injective {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {L : Subgroup G} (n : (L.map φ).Normal) : L.Normal where
  conj_mem := by
    intro a x hx
    have hx' : φ x ∈ L.map φ := ⟨x, hx, rfl⟩
    have hconj : φ a * φ x * (φ a)⁻¹ ∈ L.map φ := by
      simpa [map_mul, map_inv] using n.conj_mem hx' (φ a)
    rcases hconj with ⟨y, hy, hy_eq⟩
    apply hφ
    calc
      φ (a * x * a⁻¹) = φ a * φ x * (φ a)⁻¹ := by simp [map_mul, map_inv]
      _ = φ y := hy_eq
