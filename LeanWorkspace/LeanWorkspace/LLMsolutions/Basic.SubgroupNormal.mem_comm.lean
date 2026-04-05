FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem SubgroupNormal.mem_comm {H K : Subgroup G} (hK : H ≤ K) [hN : (H.subgroupOf K).Normal]
    {a b : G} (hb : b ∈ K) (h : a * b ∈ H) : b * a ∈ H := by
  have habK : a * b ∈ K := hK h
  have haK : a ∈ K := by
    have hrew : a = (a * b) * b⁻¹ := by simp [mul_assoc]
    rw [hrew]
    exact K.mul_mem habK (K.inv_mem hb)
  have hsub : (⟨a * b, habK⟩ : K) ∈ H.subgroupOf K := h
  have hbq : (⟨b, hb⟩ : K) ∈ (⊤ : Subgroup K) := by simp
  have hconj :
      (⟨b, hb⟩ : K) * ⟨a * b, habK⟩ * (⟨b, hb⟩ : K)⁻¹ ∈ H.subgroupOf K := by
    simpa using ((hN.conj_mem hbq).2 hsub)
  have hEq :
      (((⟨b, hb⟩ : K) * ⟨a * b, habK⟩ * (⟨b, hb⟩ : K)⁻¹ : K) : G) = b * a := by
    simp [mul_assoc]
  change (((⟨b, hb⟩ : K) * ⟨a * b, habK⟩ * (⟨b, hb⟩ : K)⁻¹ : K) : G) ∈ H at hconj
  rw [hEq] at hconj
  simpa using hconj
