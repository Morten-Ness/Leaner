import Mathlib

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_adjoin_coe_preimage {s : Set A} : Algebra.adjoin R (((↑) : Algebra.adjoin R s → A) ⁻¹' s) = ⊤ := by
  refine Algebra.eq_top_iff.2 fun ⟨x, hx⟩ ↦
      Algebra.adjoin_induction (fun a ha ↦ ?_) (fun r ↦ ?_) (fun _ _ _ _ ↦ ?_) (fun _ _ _ _ ↦ ?_) hx
  · exact Algebra.subset_adjoin ha
  · exact Subalgebra.algebraMap_mem _ r
  · exact Subalgebra.add_mem _
  · exact Subalgebra.mul_mem _

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_eq (S : Subalgebra R A) : Algebra.adjoin R ↑S = S := Algebra.adjoin_eq_of_le _ (Set.Subset.refl _) Algebra.subset_adjoin

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s ⊆ S) (h₂ : S ≤ Algebra.adjoin R s) : Algebra.adjoin R s = S := le_antisymm (Algebra.adjoin_le h₁) h₂

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

theorem adjoin_eq_ring_closure (s : Set A) :
    (Algebra.adjoin R s).toSubring = Subring.closure (Set.range (algebraMap R A) ∪ s) := .symm <| Subring.closure_eq_of_le (by simp [Algebra.adjoin]) fun x hx =>
    Subsemiring.closure_induction Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
      (fun _ _ _ _ => Subring.add_mem _) (fun _ _ _ _ => Subring.mul_mem _) hx

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_eq_sInf : Algebra.adjoin R s = sInf { p : Subalgebra R A | s ⊆ p } := le_antisymm (le_sInf fun _ h => Algebra.adjoin_le h) (sInf_le Algebra.subset_adjoin)

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_induction {p : (x : A) → x ∈ Algebra.adjoin R s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (Algebra.subset_adjoin hx))
    (algebraMap : ∀ r, p (algebraMap R A r) (algebraMap_mem _ r))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x : A} (hx : x ∈ Algebra.adjoin R s) : p x hx := let S : Subalgebra R A :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, add _ _ _ _ hpx hpy⟩
      algebraMap_mem' := fun r ↦ ⟨_, algebraMap r⟩ }
  Algebra.adjoin_le (S := S) (fun y hy ↦ ⟨Algebra.subset_adjoin hy, mem y hy⟩) hx |>.elim fun _ ↦ _root_.id

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_induction₂ {s : Set A} {p : (x y : A) → x ∈ Algebra.adjoin R s → y ∈ Algebra.adjoin R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (Algebra.subset_adjoin hx) (Algebra.subset_adjoin hy))
    (algebraMap_both : ∀ r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂) (algebraMap_mem _ r₁)
      (algebraMap_mem _ r₂))
    (algebraMap_left : ∀ (r) (x) (hx : x ∈ s), p (algebraMap R A r) x (algebraMap_mem _ r)
      (Algebra.subset_adjoin hx))
    (algebraMap_right : ∀ (r) (x) (hx : x ∈ s), p x (algebraMap R A r) (Algebra.subset_adjoin hx)
      (algebraMap_mem _ r))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    {x y : A} (hx : x ∈ Algebra.adjoin R s) (hy : y ∈ Algebra.adjoin R s) :
    p x y hx hy := by
  induction hy using Algebra.adjoin_induction with
  | mem z hz => induction hx using Algebra.adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | algebraMap r =>
    induction hx using Algebra.adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_adjoin (x : A) : Algebra.adjoin R (insert x ↑(Algebra.adjoin R s)) = Algebra.adjoin R (insert x s) := le_antisymm
    (Algebra.adjoin_le
      (Set.insert_subset_iff.mpr
        ⟨Algebra.subset_adjoin (Set.mem_insert _ _), Algebra.adjoin_mono (Set.subset_insert _ _)⟩))
    (Algebra.adjoin_mono (Set.insert_subset_insert Algebra.subset_adjoin))

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_algebraMap (x : R) (s : Set A) :
    Algebra.adjoin R (insert (algebraMap R A x) s) = Algebra.adjoin R s := by
  rw [Set.insert_eq, Algebra.adjoin_union]
  simp

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

theorem adjoin_insert_intCast (n : ℤ) (s : Set A) : Algebra.adjoin R (insert (n : A) s) = Algebra.adjoin R s := by
  simpa using Algebra.adjoin_insert_algebraMap (n : R) s

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_natCast (n : ℕ) (s : Set A) : Algebra.adjoin R (insert (n : A) s) = Algebra.adjoin R s := mod_cast Algebra.adjoin_insert_algebraMap (n : R) s

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_one (s : Set A) : Algebra.adjoin R (insert 1 s) = Algebra.adjoin R s := mod_cast Algebra.adjoin_insert_natCast R 1 s

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_zero (s : Set A) : Algebra.adjoin R (insert 0 s) = Algebra.adjoin R s := mod_cast Algebra.adjoin_insert_natCast R 0 s

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_le_centralizer_centralizer (s : Set A) :
    Algebra.adjoin R s ≤ Subalgebra.centralizer R (Subalgebra.centralizer R s) := Algebra.adjoin_le Set.subset_centralizer_centralizer

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_span {s : Set A} : Algebra.adjoin R (Submodule.span R s : Set A) = Algebra.adjoin R s := le_antisymm (Algebra.adjoin_le (Algebra.span_le_adjoin _ _)) (Algebra.adjoin_mono Submodule.subset_span)

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_union (s t : Set A) : Algebra.adjoin R (s ∪ t) = Algebra.adjoin R s ⊔ Algebra.adjoin R t := (Algebra.gc : GaloisConnection _ ((↑) : Subalgebra R A → Set A)).l_sup

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem bijective_algebraMap_iff {R A : Type*} [Field R] [Semiring A] [Nontrivial A]
    [Algebra R A] : Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ := ⟨fun h => Algebra.surjective_algebraMap_iff.1 h.2, fun h =>
    ⟨(algebraMap R A).injective, Algebra.surjective_algebraMap_iff.2 h⟩⟩

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

theorem comap_map_eq_self {f : A →ₐ[R] B} {S : Subalgebra R A}
    (h : f ⁻¹' {0} ⊆ S) : (S.map f).comap f = S := by
  convert Subalgebra.comap_map_eq f S
  rwa [left_eq_sup, Algebra.adjoin_le_iff]

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem comap_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R B).comap f = ⊤ := Algebra.eq_top_iff.2 fun _x => Algebra.mem_top

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem ext_of_eq_adjoin {S : Subalgebra R A} {s : Set A} (hS : S = Algebra.adjoin R s) ⦃φ₁ φ₂ : S →ₐ[R] B⦄
    (h : ∀ x hx, φ₁ ⟨x, hS.ge (Algebra.subset_adjoin hx)⟩ = φ₂ ⟨x, hS.ge (Algebra.subset_adjoin hx)⟩) :
    φ₁ = φ₂ := by
  subst hS; exact AlgHom.adjoin_ext h

end

section

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable {F : Type*}

variable [FunLike F A B] [AlgHomClass F R A B]

theorem ext_on_codisjoint {φ ψ : F} {S T : Subalgebra R A} (hST : Codisjoint S T)
    (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) : φ = ψ := DFunLike.ext _ _ fun _ ↦ AlgHom.eqOn_sup hS hT <| hST.eq_top.symm ▸ trivial

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem gc : GaloisConnection (Algebra.adjoin R : Set A → Subalgebra R A) (↑) := fun s S =>
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subsemiring.subset_closure) H,
   fun H => show Subsemiring.closure (Set.range (algebraMap R A) ∪ s) ≤ S.toSubsemiring from
      Subsemiring.closure_le.2 <| Set.union_subset S.range_subset H⟩

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem iInf_toSubsemiring {ι : Sort*} (S : ι → Subalgebra R A) :
    (iInf S).toSubsemiring = ⨅ i, (S i).toSubsemiring := by
  simp only [iInf, Algebra.sInf_toSubsemiring, ← Set.range_comp, Function.comp_def]

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem iSup_induction' {ι : Sort*} (S : ι → Subalgebra R A) {motive : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    {x : A} (mem : x ∈ ⨆ i, S i)
    (basic : ∀ (i) (x) (hx : x ∈ S i), motive x (Algebra.mem_iSup_of_mem i hx))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (add_mem ‹_› ‹_›))
    (mul : ∀ x y hx hy, motive x hx → motive y hy → motive (x * y) (mul_mem ‹_› ‹_›))
    (algebraMap : ∀ r, motive (algebraMap R A r) (Subalgebra.algebraMap_mem (⨆ i, S i) ‹_›)) :
    motive x mem := by
  refine Exists.elim ?_ fun (hx : x ∈ ⨆ i, S i) (hc : motive x hx) ↦ hc
  exact Algebra.iSup_induction S (motive := fun x' ↦ ∃ h, motive x' h) mem
    (fun _ _ h ↦ ⟨_, basic _ _ h⟩) (fun _ _ h h' ↦ ⟨_, add _ _ _ _ h.2 h'.2⟩)
    (fun _ _ h h' ↦ ⟨_, mul _ _ _ _ h.2 h'.2⟩) fun _ ↦ ⟨_, algebraMap _⟩

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem iSup_induction {ι : Sort*} (S : ι → Subalgebra R A) {motive : A → Prop}
    {x : A} (mem : x ∈ ⨆ i, S i)
    (basic : ∀ i, ∀ a ∈ S i, motive a)
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (algebraMap : ∀ r, motive (algebraMap R A r)) : motive x := by
  let T : Subalgebra R A :=
  { carrier := {x | motive x}
    mul_mem' {a b} := mul a b
    add_mem' {a b} := add a b
    algebraMap_mem' := algebraMap }
  suffices iSup S ≤ T from this mem
  rwa [iSup_le_iff]

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem iSup_toSubsemiring {ι : Sort*} [Nonempty ι] (S : ι → Subalgebra R A) :
    (iSup S).toSubsemiring = ⨆ i, (S i).toSubsemiring := by
  simp only [iSup, Set.range_nonempty, Algebra.sSup_toSubsemiring, ← Set.range_comp, Function.comp_def]

end

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {s : Subalgebra R S} {M : Submonoid S} {H : M ≤ s.toSubmonoid}

theorem le_saturation : s ≤ s.saturation M H := fun x hx ↦ ⟨1, one_mem M, by simpa⟩

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_bot (f : A →ₐ[R] B) : (⊥ : Subalgebra R A).map f = ⊥ := Subalgebra.toSubmodule_injective <| by
    simpa only [Subalgebra.map_toSubmodule, Algebra.toSubmodule_bot] using Submodule.map_one _

end

section

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_comap_eq (f : A →ₐ[R] B) (S : Subalgebra R B) : (S.comap f).map f = S ⊓ f.range := SetLike.coe_injective Set.image_preimage_eq_inter_range

end

section

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_comap_eq_self
    {f : A →ₐ[R] B} {S : Subalgebra R B} (h : S ≤ f.range) : (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using Subalgebra.map_comap_eq f S

end

section

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_comap_eq_self_of_surjective
    {f : A →ₐ[R] B} (hf : Function.Surjective f) (S : Subalgebra R B) : (S.comap f).map f = S := Subalgebra.map_comap_eq_self <| by simp [(AlgHom.range_eq_top f).2 hf]

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_inf (f : A →ₐ[R] B) (hf : Function.Injective f) (S T : Subalgebra R A) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R A).map f = f.range := SetLike.coe_injective Set.image_univ

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

theorem mem_adjoin_iff {s : Set A} {x : A} :
    x ∈ Algebra.adjoin R s ↔ x ∈ Subring.closure (Set.range (algebraMap R A) ∪ s) := by
  rw [← Subalgebra.mem_toSubring, Algebra.adjoin_eq_ring_closure]

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_iInf {ι : Sort*} {S : ι → Subalgebra R A} {x : A} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, Algebra.mem_sInf, Set.forall_mem_range]

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_sInf {S : Set (Subalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, Algebra.coe_sInf, Set.mem_iInter₂]

end

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {s : Subalgebra R S} {M : Submonoid S} {H : M ≤ s.toSubmonoid}

theorem mem_saturation_of_mul_mem_right {x y} (hxy : x * y ∈ s.saturation M H)
    (hy : y ∈ M) : x ∈ s.saturation M H := Subalgebra.mem_saturation_of_mul_mem_left (mul_comm x y ▸ hxy) hy

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_sup_left {S T : Subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := have : S ≤ S ⊔ T := le_sup_left; (this ·)

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_sup_right {S T : Subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T := have : T ≤ S ⊔ T := le_sup_right; (this ·)

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mul_mem_sup {S T : Subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T := (S ⊔ T).mul_mem (Algebra.mem_sup_left hx) (Algebra.mem_sup_right hy)

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem surjective_algebraMap_iff :
    Function.Surjective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ := ⟨fun h =>
    eq_bot_iff.2 fun y _ =>
      let ⟨_x, hx⟩ := h y
      hx ▸ Subalgebra.algebraMap_mem _ _,
    fun h y => Algebra.mem_bot.1 <| eq_bot_iff.1 h (Algebra.mem_top : y ∈ _)⟩

end

section

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Algebra R A]

theorem toNonUnitalSubalgebra_le_toNonUnitalSubalgebra {S T : Subalgebra R A} :
    S.toNonUnitalSubalgebra ≤ T.toNonUnitalSubalgebra ↔ S ≤ T := Subalgebra.toNonUnitalSubalgebraOrderEmbedding.le_iff_le

alias ⟨_, toNonUnitalSubalgebra_mono⟩ := toNonUnitalSubalgebra_le_toNonUnitalSubalgebra

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem toSubmodule_eq_top {S : Subalgebra R A} : Subalgebra.toSubmodule S = ⊤ ↔ S = ⊤ := Subalgebra.toSubmodule.injective.eq_iff' Algebra.top_toSubmodule

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem toSubring_bot (A : Type*) [CommRing A] (R : Subring A) :
    (⊥ : Subalgebra R A).toSubring = R := by
  aesop (add norm Subalgebra.mem_carrier.symm)

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem toSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {S : Subalgebra R A} :
    S.toSubring = ⊤ ↔ S = ⊤ := Subalgebra.toSubring_injective.eq_iff' Algebra.top_toSubring

end

section

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem toSubsemiring_eq_top {S : Subalgebra R A} : S.toSubsemiring = ⊤ ↔ S = ⊤ := Subalgebra.toSubsemiring_injective.eq_iff' Algebra.top_toSubsemiring

end
