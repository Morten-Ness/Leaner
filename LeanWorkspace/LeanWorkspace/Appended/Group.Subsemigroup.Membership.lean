import Mathlib

section

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem coe_iSup_of_directed {S : ι → Subsemigroup M} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subsemigroup M) : Set M) = ⋃ i, S i := Set.ext fun x => by simp [Subsemigroup.mem_iSup_of_directed hS]

end

section

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem coe_sSup_of_directed_on {S : Set (Subsemigroup M)} (hS : DirectedOn (· ≤ ·) S) :
    (↑(sSup S) : Set M) = ⋃ s ∈ S, ↑s := Set.ext fun x => by simp [Subsemigroup.mem_sSup_of_directed_on hS]

end

section

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem iSup_induction' (S : ι → Subsemigroup M) {C : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (mem : ∀ (i) (x) (hxS : x ∈ S i), C x (Subsemigroup.mem_iSup_of_mem i ‹_›))
    (mul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›)) {x₁ : M}
    (hx₁ : x₁ ∈ ⨆ i, S i) : C x₁ hx₁ := by
  refine Exists.elim ?_ fun (hx₁' : x₁ ∈ ⨆ i, S i) (hc : C x₁ hx₁') => hc
  refine @Subsemigroup.iSup_induction _ _ _ S (fun x' => ∃ hx'', C x' hx'') _ hx₁
      (fun i x₂ hx₂ => ?_) fun x₃ y => ?_
  · exact ⟨_, mem _ _ hx₂⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, mul _ _ _ _ Cx Cy⟩

end

section

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_iSup_of_mem {S : ι → Subsemigroup M} (i : ι) : ∀ {x : M}, x ∈ S i → x ∈ iSup S := by
  have : S i ≤ iSup S := le_iSup _ _
  tauto

end

section

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_iSup_prop {p : Prop} {S : p → Subsemigroup M} {x : M} :
    x ∈ ⨆ (h : p), S h ↔ ∃ (h : p), x ∈ S h := by
  by_cases h : p
  · simp +contextual [h]
  · simpa [h] using id

end

section

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_sSup_of_directed_on {S : Set (Subsemigroup M)} (hS : DirectedOn (· ≤ ·) S) {x : M} :
    x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  simp only [sSup_eq_iSup', Subsemigroup.mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]

end

section

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_sSup_of_mem {S : Set (Subsemigroup M)} {s : Subsemigroup M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ sSup S := by
  have : s ≤ sSup S := le_sSup hs
  tauto

end

section

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_sup_left {S T : Subsemigroup M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  have : S ≤ S ⊔ T := le_sup_left
  tauto

end

section

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_sup_right {S T : Subsemigroup M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  have : T ≤ S ⊔ T := le_sup_right
  tauto

end

section

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mul_mem_sup {S T : Subsemigroup M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T := mul_mem (Subsemigroup.mem_sup_left hx) (Subsemigroup.mem_sup_right hy)

end
