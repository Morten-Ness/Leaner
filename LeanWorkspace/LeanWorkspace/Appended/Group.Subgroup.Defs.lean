import Mathlib

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem coe_inclusion [LE S] [IsConcreteLE S G]
    {H K : S} (h : H ≤ K) (a : H) : (SubgroupClass.inclusion h a : G) = a := Set.coe_inclusion (SetLike.coe_subset_coe.mpr h) a

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {H : Subgroup G}

theorem conj_mem' (nH : H.Normal) (n : G) (hn : n ∈ H) (g : G) :
    g⁻¹ * n * g ∈ H := by
  convert nH.conj_mem n hn g⁻¹
  rw [inv_inv]

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem inclusion_inj {H K : Subgroup G} (h : H ≤ K) {x y : H} :
    Subgroup.inclusion h x = Subgroup.inclusion h y ↔ x = y := (Subgroup.inclusion_injective h).eq_iff

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {S G : Type*} [Inv G] [SetLike S G] (s : S) [HasMemOrInvMem s]

theorem inv_mem_of_notMem (x : G) (h : x ∉ s) : x⁻¹ ∈ s := by
  have := mem_or_inv_mem s x
  simp_all

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem le_normalizer : H ≤ Subgroup.normalizer H := fun x xH n => by
  rw [SetLike.mem_coe, SetLike.mem_coe, H.mul_mem_cancel_right <| H.inv_mem xH,
    H.mul_mem_cancel_left xH]

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {H : Subgroup G}

theorem mem_comm (nH : H.Normal) {a b : G} (h : a * b ∈ H) : b * a ∈ H := by
  have : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ H := nH.conj_mem (a * b) h a⁻¹
  simpa

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {H : Subgroup G}

theorem mem_comm_iff (nH : H.Normal) {a b : G} : a * b ∈ H ↔ b * a ∈ H := ⟨Subgroup.Normal.mem_comm nH, Subgroup.Normal.mem_comm nH⟩

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem mem_normalizer_iff'' {g : G} : g ∈ Subgroup.normalizer H ↔ ∀ h : G, h ∈ H ↔ g⁻¹ * h * g ∈ H := by
  rw [← Subgroup.inv_mem_iff (x := g), Subgroup.mem_normalizer_iff, inv_inv]

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem mem_normalizer_iff' {g : G} : g ∈ Subgroup.normalizer H ↔ ∀ n, n * g ∈ H ↔ g * n ∈ H := ⟨fun h n ↦ by rw [← SetLike.mem_coe, ← SetLike.mem_coe, h, mul_assoc, mul_inv_cancel_right],
    fun h n ↦ by rw [SetLike.mem_coe, SetLike.mem_coe, mul_assoc, ← h, inv_mul_cancel_right]⟩

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {S G : Type*} [Inv G] [SetLike S G] (s : S) [HasMemOrInvMem s]

theorem mem_of_inv_notMem (x : G) (h : x⁻¹ ∉ s) : x ∈ s := by
  have := mem_or_inv_mem s x
  simp_all

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

theorem subset_union [LE S] [IsConcreteLE S G] {H K L : S} :
    (H : Set G) ⊆ K ∪ L ↔ H ≤ K ∨ H ≤ L := by
  refine ⟨fun h ↦ ?_, fun h x xH ↦ h.imp (mem_of_le_of_mem · xH) (mem_of_le_of_mem · xH)⟩
  rw [or_iff_not_imp_left, SetLike.not_le_iff_exists, ← SetLike.coe_subset_coe]
  exact fun ⟨x, xH, xK⟩ y yH ↦ (h <| mul_mem xH yH).elim
    ((h yH).resolve_left fun yK ↦ xK <| (mul_mem_cancel_right yK).mp ·)
    (mul_mem_cancel_left <| (h xH).resolve_left xK).mp

end

section

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem toSubmonoid_inj {p q : Subgroup G} : p.toSubmonoid = q.toSubmonoid ↔ p = q := Subgroup.toSubmonoid_injective.eq_iff

end
