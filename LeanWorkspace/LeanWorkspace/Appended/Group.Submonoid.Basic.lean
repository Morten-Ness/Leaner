import Mathlib

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ Submonoid.closure s) : Submonoid.closure s = S := le_antisymm (Submonoid.closure_le.2 h₁) h₂

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_eq_one_union (s : Set M) :
    Submonoid.closure s = {(1 : M)} ∪ (Subsemigroup.closure s : Set M) := by
  apply le_antisymm
  · intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx => exact Or.inr <| Subsemigroup.subset_closure hx
    | one => exact Or.inl <| by simp
    | mul x hx y hy hx hy =>
      push _ ∈ _ at hx hy
      obtain ⟨(rfl | hx), (rfl | hy)⟩ := And.intro hx hy
      all_goals simp_all [mul_mem]
  · rintro x (hx | hx)
    · exact (show x = 1 by simpa using hx) ▸ one_mem (Submonoid.closure s)
    · exact Subsemigroup.closure_le.mpr Submonoid.subset_closure hx

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_induction {s : Set M} {motive : (x : M) → x ∈ Submonoid.closure s → Prop}
    (mem : ∀ (x) (h : x ∈ s), motive x (Submonoid.subset_closure h)) (one : motive 1 (one_mem _))
    (mul : ∀ x y hx hy, motive x hx → motive y hy → motive (x * y) (mul_mem hx hy)) {x}
    (hx : x ∈ Submonoid.closure s) : motive x hx := let S : Submonoid M :=
    { carrier := { x | ∃ hx, motive x hx }
      one_mem' := ⟨_, one⟩
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩ }
  Submonoid.closure_le (S := S) |>.mpr (fun y hy ↦ ⟨Submonoid.subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_induction₂ {motive : (x y : M) → x ∈ Submonoid.closure s → y ∈ Submonoid.closure s → Prop}
    (mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), motive x y (Submonoid.subset_closure hx) (Submonoid.subset_closure hy))
    (one_left : ∀ x hx, motive 1 x (one_mem _) hx) (one_right : ∀ x hx, motive x 1 hx (one_mem _))
    (mul_left : ∀ x y z hx hy hz,
      motive x z hx hz → motive y z hy hz → motive (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz,
      motive z x hz hx → motive z y hz hy → motive z (x * y) hz (mul_mem hx hy))
    {x y : M} (hx : x ∈ Submonoid.closure s) (hy : y ∈ Submonoid.closure s) : motive x y hx hy := by
  induction hy using Submonoid.closure_induction with
  | mem z hz => induction hx using Submonoid.closure_induction with
    | mem _ h => exact mem _ _ h hz
    | one => exact one_left _ (Submonoid.subset_closure hz)
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ hx h₁ h₂

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

variable {t : Set M}

theorem closure_sdiff_eq_closure (hts : t ⊆ Submonoid.closure (s \ t)) : Submonoid.closure (s \ t) = Submonoid.closure s := by
  refine (Submonoid.closure_mono Set.diff_subset).antisymm <| Submonoid.closure_le.mpr <| fun x hxs ↦ ?_
  by_cases hxt : x ∈ t
  · exact hts hxt
  · rw [SetLike.mem_coe, Submonoid.mem_closure]
    exact fun N hN ↦ hN <| Set.mem_diff_of_mem hxs hxt

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

variable {t : Set M}

theorem closure_sdiff_singleton_one (s : Set M) : Submonoid.closure (s \ {1}) = Submonoid.closure s := Submonoid.closure_sdiff_eq_closure <| by simp [one_mem]

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem coe_iInf {ι : Sort*} {S : ι → Submonoid M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [iInf, Submonoid.coe_sInf, Set.biInter_range]

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem disjoint_def' {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ ∀ {x y : M}, x ∈ p₁ → y ∈ p₂ → x = y → x = 1 := Submonoid.disjoint_def.trans ⟨fun h _ _ hx hy hxy => h hx <| hxy.symm ▸ hy, fun h _ hx hx' => h hx hx' rfl⟩

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable [MulOneClass N]

theorem eqOn_closureM {f g : M →* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (Submonoid.closure s) := show Submonoid.closure s ≤ f.eqLocusM g from Submonoid.closure_le.2 h

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem iSup_eq_closure {ι : Sort*} (p : ι → Submonoid M) :
    ⨆ i, p i = Submonoid.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Submonoid.closure_iUnion, Submonoid.closure_eq]

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem mem_iInf {ι : Sort*} {S : ι → Submonoid M} {x : M} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, Submonoid.mem_sInf, Set.forall_mem_range]

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem mem_iSup {ι : Sort*} (p : ι → Submonoid M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← Submonoid.closure_singleton_le_iff_mem, le_iSup_iff]
  simp only [Submonoid.closure_singleton_le_iff_mem]

end

section

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem sup_eq_closure (N N' : Submonoid M) : N ⊔ N' = Submonoid.closure ((N : Set M) ∪ (N' : Set M)) := by
  simp_rw [Submonoid.closure_union, Submonoid.closure_eq]

end
