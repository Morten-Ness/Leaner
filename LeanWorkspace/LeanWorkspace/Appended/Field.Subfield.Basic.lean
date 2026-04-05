import Mathlib

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_eq_of_le {s : Set K} {t : Subfield K} (h₁ : s ⊆ t) (h₂ : t ≤ Subfield.closure s) :
    Subfield.closure s = t := le_antisymm (Subfield.closure_le.2 h₁) h₂

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_induction {s : Set K} {p : ∀ x ∈ Subfield.closure s, Prop}
    (mem : ∀ x hx, p x (Subfield.subset_closure hx))
    (one : p 1 (one_mem _)) (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (neg : ∀ x hx, p x hx → p (-x) (neg_mem hx)) (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (h : x ∈ Subfield.closure s) : p x h := letI : Subfield K :=
    { carrier := {x | ∃ hx, p x hx}
      mul_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, mul _ _ _ _ hx hy⟩
      one_mem' := ⟨_, one⟩
      add_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, add _ _ _ _ hx hy⟩
      zero_mem' := ⟨zero_mem _, by
        simp_rw [← @add_neg_cancel K _ 1]; exact add _ _ _ _ one (neg _ _ one)⟩
      neg_mem' := by rintro _ ⟨_, hx⟩; exact ⟨_, neg _ _ hx⟩
      inv_mem' := by rintro _ ⟨_, hx⟩; exact ⟨_, inv _ _ hx⟩ }
  ((Subfield.closure_le (t := this)).2 (fun x hx ↦ ⟨_, mem x hx⟩) h).2

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_le {s : Set K} {t : Subfield K} : Subfield.closure s ≤ t ↔ s ⊆ t := ⟨Set.Subset.trans Subfield.subset_closure, fun h _ hx => Subfield.mem_closure.mp hx t h⟩

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Set K}

theorem closure_preimage_le (f : K →+* L) (s : Set L) : Subfield.closure (f ⁻¹' s) ≤ (Subfield.closure s).comap f := Subfield.closure_le.2 fun _ hx => SetLike.mem_coe.2 <| Subfield.mem_comap.2 <| Subfield.subset_closure hx

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_iInf {ι : Sort*} {S : ι → Subfield K} : (↑(⨅ i, S i) : Set K) = ⋂ i, S i := by
  simp only [iInf, Subfield.coe_sInf, Set.biInter_range]

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subfield K) : Set K) = ⋃ i, ↑(S i) := Set.ext fun x => by simp [Subfield.mem_iSup_of_directed hS]

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield K) : Set K) = ⋂ s ∈ S, ↑s := show ((sInf (Subfield.toSubring '' S) : Subring K) : Set K) = ⋂ s ∈ S, ↑s by simp

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set K) = ⋃ s ∈ S, ↑s := Set.ext fun x => by simp [Subfield.mem_sSup_of_directedOn Sne hS]

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

variable {L : Type v} [Semiring L]

theorem eqOn_field_closure {f g : K →+* L} {s : Set K} (h : Set.EqOn f g s) :
    Set.EqOn f g (Subfield.closure s) := show Subfield.closure s ≤ f.eqLocusField g from Subfield.closure_le.2 h

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

variable {L : Type v} [Semiring L]

theorem eq_of_eqOn_of_field_closure_eq_top {s : Set K} (hs : Subfield.closure s = ⊤) {f g : K →+* L}
    (h : s.EqOn f g) : f = g := RingHom.eq_of_eqOn_subfield_top <| hs ▸ RingHom.eqOn_field_closure h

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (g : L →+* M) (f : K →+* L)

theorem fieldRange_eq_top_iff {f : K →+* L} :
    f.fieldRange = ⊤ ↔ Function.Surjective f := SetLike.ext'_iff.trans Set.range_eq_univ

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

theorem field_closure_preimage_le (f : K →+* L) (s : Set L) :
    Subfield.closure (f ⁻¹' s) ≤ (Subfield.closure s).comap f := Subfield.closure_le.2 fun _ hx => SetLike.mem_coe.2 <| Subfield.mem_comap.2 <| Subfield.subset_closure hx

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

variable (f : K →+* L)

theorem gc_map_comap (f : K →+* L) : GaloisConnection (Subfield.map f) (Subfield.comap f) := fun _ _ =>
  Subfield.map_le_iff_le_comap

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (g : L →+* M) (f : K →+* L)

theorem map_fieldRange : f.fieldRange.map g = (g.comp f).fieldRange := by
  simpa only [RingHom.fieldRange_eq_map] using Subfield.map_map (⊤ : Subfield K) g f

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

theorem map_field_closure (f : K →+* L) (s : Set K) : (Subfield.closure s).map f = Subfield.closure (f '' s) := Set.image_preimage.l_comm_of_u_comm (Subfield.gc_map_comap f) (Subfield.gi L).gc (Subfield.gi K).gc
    fun _ ↦ rfl

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem map_inf (s t : Subfield K) (f : K →+* L) : (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter f.injective)

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

variable (f : K →+* L)

theorem map_map (g : L →+* M) (f : K →+* L) : (s.map f).map g = s.map (g.comp f) := SetLike.ext' <| Set.image_image _ _ _

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

variable (f : K →+* L)

theorem map_mem_map (f : K →+* L) {s : Subfield K} {x : K} : f x ∈ s.map f ↔ x ∈ s := calc
    _ ↔ f x ∈ (s.map f : Set L) := Iff.rfl
    _ ↔ _ := by simp [Function.Injective.mem_set_image (f := f) f.injective]

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_iInf {ι : Sort*} {S : ι → Subfield K} {x : K} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, Subfield.mem_sInf, Set.forall_mem_range]

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S)
    {x : K} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  let s : Subfield K :=
    { __ := Subring.copy _ _ (Subring.coe_iSup_of_directed hS).symm
      inv_mem' := fun _ hx ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (S i).inv_mem hi⟩ }
  have : iSup S = s := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set K)) i) (Set.iUnion_subset fun _ ↦ le_iSup S _)
  exact this ▸ Set.mem_iUnion

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_sInf {S : Set (Subfield K)} {x : K} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simpa only [Set.mem_iInter] using Set.ext_iff.1 (Subfield.coe_sInf S) x

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S)
    {x : K} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', Subfield.mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

theorem rangeRestrictField_bijective (f : K →+* L) : Function.Bijective (RingHom.rangeRestrictField f) := (Equiv.ofInjective f f.injective).bijective

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem sInf_toSubring (s : Set (Subfield K)) :
    (sInf s).toSubring = ⨅ t ∈ s, Subfield.toSubring t := by
  ext x
  simp [Subfield.mem_sInf]

end

section

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem subring_closure_le (s : Set K) : Subring.closure s ≤ (Subfield.closure s).toSubring := Subring.closure_le.mpr Subfield.subset_closure

end
