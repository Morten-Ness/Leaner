import Mathlib

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem bot_or_exists_ne_one (H : Subgroup G) : H = ⊥ ∨ ∃ x ∈ H, x ≠ (1 : G) := by
  convert H.bot_or_nontrivial
  rw [Subgroup.nontrivial_iff_exists_ne_one]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem bot_or_nontrivial (H : Subgroup G) : H = ⊥ ∨ Nontrivial H := by
  have := Subgroup.nontrivial_iff_ne_bot H
  tauto

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_closure_coe_preimage {k : Set G} : Subgroup.closure (((↑) : Subgroup.closure k → G) ⁻¹' k) = ⊤ := eq_top_iff.2 fun x _ ↦ Subtype.recOn x fun _ hx' ↦
    Subgroup.closure_induction (fun _ h ↦ Subgroup.subset_closure h) (one_mem _) (fun _ _ _ _ ↦ mul_mem)
      (fun _ _ ↦ inv_mem) hx'

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_eq_bot_iff : Subgroup.closure k = ⊥ ↔ k ⊆ {1} := le_bot_iff.symm.trans <| Subgroup.closure_le _

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_eq_of_le (h₁ : k ⊆ K) (h₂ : K ≤ Subgroup.closure k) : Subgroup.closure k = K := le_antisymm ((Subgroup.closure_le <| K).2 h₁) h₂

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_eq_top_of_mclosure_eq_top {S : Set G} (h : Submonoid.closure S = ⊤) :
    Subgroup.closure S = ⊤ := (Subgroup.eq_top_iff' _).2 fun _ => Subgroup.le_closure_toSubmonoid _ <| h.symm ▸ trivial

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_induction {p : (g : G) → g ∈ Subgroup.closure k → Prop}
    (mem : ∀ x (hx : x ∈ k), p x (Subgroup.subset_closure hx)) (one : p 1 (one_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx)) {x} (hx : x ∈ Subgroup.closure k) : p x hx := let K : Subgroup G :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, ha⟩ ⟨_, hb⟩ ↦ ⟨_, mul _ _ _ _ ha hb⟩
      one_mem' := ⟨_, one⟩
      inv_mem' := fun ⟨_, hb⟩ ↦ ⟨_, inv _ _ hb⟩ }
  Subgroup.closure_le (K := K) |>.mpr (fun y hy ↦ ⟨Subgroup.subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_induction₂ {p : (x y : G) → x ∈ Subgroup.closure k → y ∈ Subgroup.closure k → Prop}
    (mem : ∀ (x) (y) (hx : x ∈ k) (hy : y ∈ k), p x y (Subgroup.subset_closure hx) (Subgroup.subset_closure hy))
    (one_left : ∀ x hx, p 1 x (one_mem _) hx) (one_right : ∀ x hx, p x 1 hx (one_mem _))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ y z x hy hz hx, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    (inv_left : ∀ x y hx hy, p x y hx hy → p x⁻¹ y (inv_mem hx) hy)
    (inv_right : ∀ x y hx hy, p x y hx hy → p x y⁻¹ hx (inv_mem hy))
    {x y : G} (hx : x ∈ Subgroup.closure k) (hy : y ∈ Subgroup.closure k) : p x y hx hy := by
  induction hy using Subgroup.closure_induction with
  | mem z hz => induction hx using Subgroup.closure_induction with
    | mem _ h => exact mem _ _ h hz
    | one => exact one_left _ (Subgroup.subset_closure hz)
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | inv _ _ h => exact inv_left _ _ _ _ h
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ hx h₁ h₂
  | inv _ _ h => exact inv_right _ _ _ _ h

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_singleton_one : Subgroup.closure ({1} : Set G) = ⊥ := by
  simp [Subgroup.eq_bot_iff_forall, Subgroup.mem_closure_singleton]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_eq_singleton {H : Subgroup G} : (∃ g : G, (H : Set G) = {g}) ↔ H = ⊥ := ⟨fun ⟨g, hg⟩ =>
    haveI : Subsingleton (H : Set G) := by
      rw [hg]
      infer_instance
    H.eq_bot_of_subsingleton,
    fun h => ⟨1, SetLike.ext'_iff.mp h⟩⟩

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_eq_univ {H : Subgroup G} : (H : Set G) = Set.univ ↔ H = ⊤ := (SetLike.ext'_iff.trans (by rfl)).symm

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_iInf {ι : Sort*} {S : ι → Subgroup G} : (↑(⨅ i, S i) : Set G) = ⋂ i, S i := by
  simp only [iInf, Subgroup.coe_sInf, Set.biInter_range]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem coe_iSup_of_directed {ι} [Nonempty ι] {S : ι → Subgroup G} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subgroup G) : Set G) = ⋃ i, S i := Set.ext fun x ↦ by simp [Subgroup.mem_iSup_of_directed hS]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem disjoint_def' {H₁ H₂ : Subgroup G} :
    Disjoint H₁ H₂ ↔ ∀ {x y : G}, x ∈ H₁ → y ∈ H₂ → x = y → x = 1 := Subgroup.disjoint_def.trans ⟨fun h _x _y hx hy hxy ↦ h hx <| hxy.symm ▸ hy, fun h _x hx hx' ↦ h hx hx' rfl⟩

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem disjoint_def {H₁ H₂ : Subgroup G} : Disjoint H₁ H₂ ↔ ∀ {x : G}, x ∈ H₁ → x ∈ H₂ → x = 1 := disjoint_iff_inf_le.trans <| by simp only [SetLike.le_def, Subgroup.mem_inf, Subgroup.mem_bot, and_imp]

end

section

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

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem eq_bot_of_subsingleton [Subsingleton H] : H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rw [← Subgroup.coe_mk H y hy, Subsingleton.elim (⟨y, hy⟩ : H) 1, Subgroup.coe_one]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem eq_top_iff' : H = ⊤ ↔ ∀ x : G, x ∈ H := eq_top_iff.trans ⟨fun h m => h <| Subgroup.mem_top m, fun h m _ => h m⟩

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem exists_ne_one_of_nontrivial (H : Subgroup G) [Nontrivial H] :
    ∃ x ∈ H, x ≠ 1 := by
  rwa [← Subgroup.nontrivial_iff_exists_ne_one]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem iSup_eq_closure {ι : Sort*} (p : ι → Subgroup G) :
    ⨆ i, p i = Subgroup.closure (⋃ i, (p i : Set G)) := by simp_rw [Subgroup.closure_iUnion, Subgroup.closure_eq]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem le_closure_toSubmonoid (S : Set G) : Submonoid.closure S ≤ (Subgroup.closure S).toSubmonoid := Submonoid.closure_le.2 Subgroup.subset_closure

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem mem_closure_pair {x y z : C} :
    z ∈ Subgroup.closure ({x, y} : Set C) ↔ ∃ m n : ℤ, x ^ m * y ^ n = z := by
  rw [← Set.singleton_union, Subgroup.closure_union, Subgroup.mem_sup]
  simp_rw [Subgroup.mem_closure_singleton, exists_exists_eq_and]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_closure_singleton_self (x : G) : x ∈ Subgroup.closure ({x} : Set G) := by
  simpa [-Subgroup.subset_closure] using Subgroup.subset_closure (k := {x})

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_iInf {ι : Sort*} {S : ι → Subgroup G} {x : G} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, Subgroup.mem_sInf, Set.forall_mem_range]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Subgroup G} (i : ι) :
    ∀ {x : G}, x ∈ S i → x ∈ iSup S := have : S i ≤ iSup S := le_iSup _ _; fun h ↦ this h

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_iSup_prop {p : Prop} {K : p → Subgroup G} {x : G} :
    x ∈ ⨆ (h : p), K h ↔ x = 1 ∨ ∃ (h : p), x ∈ K h := by
  by_cases h : p <;>
  simp +contextual [h]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_sSup_of_directedOn {K : Set (Subgroup G)} (Kne : K.Nonempty) (hK : DirectedOn (· ≤ ·) K)
    {x : G} : x ∈ sSup K ↔ ∃ s ∈ K, x ∈ s := by
  haveI : Nonempty K := Kne.to_subtype
  simp only [sSup_eq_iSup', Subgroup.mem_iSup_of_directed hK.directed_val, SetCoe.exists, exists_prop]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_sSup_of_mem {S : Set (Subgroup G)} {s : Subgroup G} (hs : s ∈ S) :
    ∀ {x : G}, x ∈ s → x ∈ sSup S := have : s ≤ sSup S := le_sSup hs; fun h ↦ this h

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

theorem mem_sup' : x ∈ s ⊔ t ↔ ∃ (y : s) (z : t), (y : C) * z = x := Subgroup.mem_sup.trans <| by simp only [SetLike.exists, exists_prop]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

theorem mem_sup : x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := ⟨fun h => by
    rw [Subgroup.sup_eq_closure] at h
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ h
    · rintro y (h | h)
      · exact ⟨y, h, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, y, h, by simp⟩
    · exact ⟨1, s.one_mem, 1, ⟨t.one_mem, mul_one 1⟩⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨_, mul_mem hy₁ hy₂, _, mul_mem hz₁ hz₂, by simp [mul_assoc, mul_left_comm]⟩
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      exact ⟨_, inv_mem hy, _, inv_mem hz, mul_comm z y ▸ (mul_inv_rev z y).symm⟩, by
    rintro ⟨y, hy, z, hz, rfl⟩; exact Subgroup.mul_mem_sup hy hz⟩

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_sup_left {S T : Subgroup G} : ∀ {x : G}, x ∈ S → x ∈ S ⊔ T := have : S ≤ S ⊔ T := le_sup_left; fun h ↦ this h

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem mem_sup_of_normal_left {s t : Subgroup G} [hs : s.Normal] {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  have h := (sup_comm t s) ▸ Subgroup.mem_sup_of_normal_right (s := t) (t := s) (x := x)
  exact h.trans
    ⟨fun ⟨y, hy, z, hz, hp⟩ ↦ ⟨y * z * y⁻¹, hs.conj_mem z hz y, y, hy, by simp [hp]⟩,
    fun ⟨y, hy, z, hz, hp⟩ ↦ ⟨z, hz, z⁻¹ * y * z, hs.conj_mem' y hy z, by simp [mul_assoc, hp]⟩⟩

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem mem_sup_of_normal_right {s t : Subgroup G} [ht : t.Normal] {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro hx; rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, x, hx, by simp⟩
    · exact ⟨1, s.one_mem, 1, t.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨y₁ * y₂, s.mul_mem hy₁ hy₂,
            (y₂⁻¹ * z₁ * y₂) * z₂, t.mul_mem (ht.conj_mem' z₁ hz₁ y₂) hz₂, by simp [mul_assoc]⟩
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      exact ⟨y⁻¹, s.inv_mem hy,
            y * z⁻¹ * y⁻¹, ht.conj_mem z⁻¹ (t.inv_mem hz) y, by simp [mul_assoc]⟩
  · rintro ⟨y, hy, z, hz, rfl⟩; exact Subgroup.mul_mem_sup hy hz

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_sup_right {S T : Subgroup G} : ∀ {x : G}, x ∈ T → x ∈ S ⊔ T := have : T ≤ S ⊔ T := le_sup_right; fun h ↦ this h

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mul_mem_sup {S T : Subgroup G} {x y : G} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T := (S ⊔ T).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem nontrivial_iff_exists_ne_one (H : Subgroup G) : Nontrivial H ↔ ∃ x ∈ H, x ≠ (1 : G) := by
  rw [Subtype.nontrivial_iff_exists_ne (fun x => x ∈ H) (1 : H)]
  simp

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem nontrivial_iff_ne_bot (H : Subgroup G) : Nontrivial H ↔ H ≠ ⊥ := by
  rw [Subgroup.nontrivial_iff_exists_ne_one, ne_eq, Subgroup.eq_bot_iff_forall]
  simp only [ne_eq, not_forall, exists_prop]

end

section

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem sup_eq_closure (H H' : Subgroup G) : H ⊔ H' = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  simp_rw [Subgroup.closure_union, Subgroup.closure_eq]

end
