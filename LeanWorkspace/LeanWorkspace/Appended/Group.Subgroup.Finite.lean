import Mathlib

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_eq_iff_eq_top [Finite H] : Nat.card H = Nat.card G ↔ H = ⊤ := Iff.intro (Subgroup.eq_top_of_card_eq H) (fun h ↦ by simpa only [h] using Subgroup.card_top)

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_le_card_group [Finite G] : Nat.card H ≤ Nat.card G := Nat.card_le_card_of_injective _ Subtype.coe_injective

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_le_of_le {H K : Subgroup G} [Finite K] (h : H ≤ K) : Nat.card H ≤ Nat.card K := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h)

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_le_one_iff_eq_bot [Finite H] : Nat.card H ≤ 1 ↔ H = ⊥ := ⟨H.eq_bot_of_card_le, fun h => by simp [h]⟩

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_top : Nat.card (⊤ : Subgroup G) = Nat.card G := Nat.card_congr Subgroup.topEquiv.toEquiv

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem eq_of_le_of_card_ge {H K : Subgroup G} [Finite K] (hle : H ≤ K)
    (hcard : Nat.card K ≤ Nat.card H) :
    H = K := SetLike.coe_injective <| Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle hcard

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem eq_top_of_card_eq [Finite H] (h : Nat.card H = Nat.card G) : H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ Nat.card_pos.ne')
  exact Subgroup.eq_top_of_le_card _ (Nat.le_of_eq h.symm)

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem eq_top_of_le_card [Finite G] (h : Nat.card G ≤ Nat.card H) : H = ⊤ := Subgroup.eq_of_le_of_card_ge le_top (Nat.card_congr (Equiv.Set.univ G) ▸ h)

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

theorem mem_normalizer_fintype {S : Set G} [Finite S] {x : G} (h : ∀ n, n ∈ S → x * n * x⁻¹ ∈ S) :
    x ∈ Subgroup.normalizer S := by
  haveI := Classical.propDecidable; cases nonempty_fintype S
  exact fun n =>
    ⟨h n, fun h₁ =>
      have heq : (fun n => x * n * x⁻¹) '' S = S :=
        Set.eq_of_subset_of_card_le (fun n ⟨y, hy⟩ => hy.2 ▸ h y hy.1)
          (by rw [Set.card_image_of_injective S conj_injective])
      have : x * n * x⁻¹ ∈ (fun n => x * n * x⁻¹) '' S := heq.symm ▸ h₁
      let ⟨y, hy⟩ := this
      conj_injective hy.2 ▸ hy.1⟩

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem multiset_noncommProd_mem (K : Subgroup G) (g : Multiset G) (comm) :
    (∀ a ∈ g, a ∈ K) → g.noncommProd comm ∈ K := K.toSubmonoid.multiset_noncommProd_mem g comm

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem noncommProd_mem (K : Subgroup G) {ι : Type*} {t : Finset ι} {f : ι → G} (comm) :
    (∀ c ∈ t, f c ∈ K) → t.noncommProd f comm ∈ K := K.toSubmonoid.noncommProd_mem t f comm

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem one_lt_card_iff_ne_bot [Finite H] : 1 < Nat.card H ↔ H ≠ ⊥ := lt_iff_not_ge.trans H.card_le_one_iff_eq_bot.not

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : Subgroup (∀ i, f i)} (x : ∀ i, f i)
    (h : ∀ i, Pi.mulSingle i (x i) ∈ H) : x ∈ H := Submonoid.pi_mem_of_mulSingle_mem x h

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

theorem pi_mem_of_mulSingle_mem_aux [DecidableEq η] (I : Finset η) {H : Subgroup (∀ i, f i)}
    (x : ∀ i, f i) (h1 : ∀ i, i ∉ I → x i = 1) (h2 : ∀ i, i ∈ I → Pi.mulSingle i (x i) ∈ H) :
    x ∈ H := Submonoid.pi_mem_of_mulSingle_mem_aux I x h1 h2

end
