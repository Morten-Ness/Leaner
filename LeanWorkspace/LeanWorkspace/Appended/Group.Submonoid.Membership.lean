import Mathlib

section

variable {M A B : Type*}

variable [MulOneClass M]

theorem coe_iSup_of_directed {ι} [Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Submonoid M) : Set M) = ⋃ i, S i := Set.ext fun x ↦ by simp [Submonoid.mem_iSup_of_directed hS]

end

section

variable {M A B : Type*}

variable [MulOneClass M]

theorem coe_sSup_of_directedOn {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set M) = ⋃ s ∈ S, ↑s := Set.ext fun x => by simp [Submonoid.mem_sSup_of_directedOn Sne hS]

end

section

variable {M A B : Type*}

variable {N : Type*} [CommMonoid N]

variable {P : N → Prop}

theorem forall_mem_sup {s t : Submonoid N} :
    (∀ x ∈ s ⊔ t, P x) ↔ (∀ x₁ ∈ s, ∀ x₂ ∈ t, P (x₁ * x₂)) := by
  simp [Submonoid.mem_sup]
  aesop

end

section

variable {M A B : Type*}

variable [MulOneClass M]

theorem iSup_induction' {ι : Sort*} (S : ι → Submonoid M) {motive : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (mem : ∀ (i), ∀ (x) (hxS : x ∈ S i), motive x (Submonoid.mem_iSup_of_mem i hxS))
    (one : motive 1 (one_mem _))
    (mul : ∀ x y hx hy, motive x hx → motive y hy → motive (x * y) (mul_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, S i) : motive x hx := by
  refine Exists.elim (?_ : ∃ Hx, motive x Hx) fun (hx : x ∈ ⨆ i, S i) (hc : motive x hx) => hc
  refine @Submonoid.iSup_induction _ _ ι S (fun m => ∃ hm, motive m hm) _ hx (fun i x hx => ?_) ?_
      fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, one⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, mul _ _ _ _ Cx Cy⟩

end

section

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem log_mul [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (x y : Submonoid.powers (n : M)) : Submonoid.log (x * y) = Submonoid.log x + Submonoid.log y := map_mul (Submonoid.powLogEquiv h).symm x y

end

section

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem log_pow_eq_self [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (m : ℕ) : Submonoid.log (Submonoid.pow n m) = m := Submonoid.pow_right_injective_iff_pow_injective.mp h <| Submonoid.pow_log_eq_self _

end

section

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem log_pow_int_eq_self {x : ℤ} (h : 1 < x.natAbs) (m : ℕ) : Submonoid.log (Submonoid.pow x m) = m := (Submonoid.powLogEquiv (Int.pow_right_injective h)).symm_apply_apply _

end

section

variable {M A B : Type*}

theorem mem_closure_pair {A : Type*} [CommMonoid A] (a b c : A) :
    c ∈ Submonoid.closure ({a, b} : Set A) ↔ ∃ m n : ℕ, a ^ m * b ^ n = c := by
  rw [← Set.singleton_union, Submonoid.closure_union, Submonoid.mem_sup]
  simp_rw [Submonoid.mem_closure_singleton, exists_exists_eq_and]

end

section

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Submonoid M} (i : ι) :
    ∀ {x : M}, x ∈ S i → x ∈ iSup S := by
  rw [← SetLike.le_def]
  exact le_iSup _ _

end

section

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_iSup_prop {p : Prop} {S : p → Submonoid M} {x : M} :
    x ∈ ⨆ (h : p), S h ↔ x = 1 ∨ ∃ (h : p), x ∈ S h := by
  by_cases h : p <;>
  simp +contextual [h]

end

section

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem mem_powers_iff (x z : M) : x ∈ Submonoid.powers z ↔ ∃ n : ℕ, z ^ n = x := Iff.rfl

noncomputable instance decidableMemPowers : DecidablePred (· ∈ Submonoid.powers a) :=
  Classical.decPred _

-- TODO the following instance should follow from a more general principle
-- See also https://github.com/leanprover-community/mathlib4/issues/2417
noncomputable instance fintypePowers [Fintype M] : Fintype (Submonoid.powers a) :=
  inferInstanceAs <| Fintype {y // y ∈ Submonoid.powers a}

end

section

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_sSup_of_directedOn {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : M} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp [sSup_eq_iSup', Submonoid.mem_iSup_of_directed hS.directed_val]

end

section

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_sSup_of_mem {S : Set (Submonoid M)} {s : Submonoid M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ sSup S := by
  rw [← SetLike.le_def]
  exact le_sSup hs

end

section

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_sup_left {S T : Submonoid M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_left

end

section

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_sup_right {S T : Submonoid M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_right

end

section

variable {M A B : Type*}

variable [MulOneClass M]

theorem mul_mem_sup {S T : Submonoid M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T := (S ⊔ T).mul_mem (Submonoid.mem_sup_left hx) (Submonoid.mem_sup_right hy)

end

section

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem pow_log_eq_self [DecidableEq M] {n : M} (p : Submonoid.powers n) : Submonoid.pow n (Submonoid.log p) = p := Subtype.ext <| Nat.find_spec p.prop

end

section

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem pow_right_injective_iff_pow_injective {n : M} :
    (Function.Injective fun m : ℕ => n ^ m) ↔ Function.Injective (Submonoid.pow n) := Subtype.coe_injective.of_comp_iff (Submonoid.pow n)

end

section

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem powers_le {n : M} {P : Submonoid M} : Submonoid.powers n ≤ P ↔ n ∈ P := by simp [Submonoid.powers_eq_closure]

end

section

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem powers_one : Submonoid.powers (1 : M) = ⊥ := bot_unique <| Submonoid.powers_le.2 <| one_mem _

end
