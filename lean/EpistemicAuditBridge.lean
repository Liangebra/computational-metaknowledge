import EpistemicCeiling
import EpistemicCoverageMeasure
import EpistemicModal

namespace EpistemicAuditBridge

open EpistemicCeiling
open EpistemicSelfKnowledge.CoverageMeasure
open scoped ENNReal BigOperators

private theorem select_representative (obs : ℕ → ℕ) (ho : Computable obs)
    (hs : Function.Surjective obs) :
    ∃ rep : ℕ → ℕ, Computable rep ∧ ∀ i, obs (rep i) = i := by
  let test (a : ℕ × ℕ) := obs a.2 == a.1
  have htest : Computable test :=
    (Primrec.beq (α := ℕ)).to_comp.comp (ho.comp Computable.snd) Computable.fst
  have hex (i : ℕ) : ∃ s, test (i, s) = true := by
    obtain ⟨s, hs'⟩ := hs i
    exact ⟨s, by simp [test, hs']⟩
  obtain ⟨rep, hr, hok⟩ := computable_search htest hex
  exact ⟨rep, hr, fun i => by simpa [test] using hok i⟩

abbrev Certifier := ℕ × (Bool × ℕ) → Bool

def Certified (verify : Certifier) (i : ℕ) : Prop :=
  ∃ b w, verify (i, (b, w)) = true

def SoundCertifier (obs : ℕ → ℕ) (atom : ℕ → Bool) (verify : Certifier) : Prop :=
  Sound obs atom (fun i b w => verify (i, (b, w)))

theorem computable_certified_re (verify : Certifier) (hv : Computable verify) :
    REPred (Certified verify) := by
  let test (a : ℕ × ℕ) := verify (a.1, (false, a.2)) || verify (a.1, (true, a.2))
  have hb (b : Bool) : Computable fun a : ℕ × ℕ => verify (a.1, (b, a.2)) :=
    hv.comp (Computable.fst.pair ((Computable.const b).pair Computable.snd))
  have ht : Computable test := Primrec.or.to_comp.comp (hb false) (hb true)
  apply (re_exists_test ht).of_eq
  intro i
  constructor
  · rintro ⟨w, hw⟩
    have hw' : verify (i, (false, w)) = true ∨ verify (i, (true, w)) = true := by
      simpa [test] using hw
    exact hw'.elim (fun h => ⟨false, w, h⟩) (fun h => ⟨true, w, h⟩)
  · rintro ⟨b, w, hw⟩
    cases b <;> exact ⟨w, by simp [test, hw]⟩

private theorem exact_domain_certifier (obs : ℕ → ℕ) (atom : ℕ → Bool)
    (ho : Computable obs) (ha : Computable atom) (hs : Function.Surjective obs)
    {Q : ℕ → Prop} (hQ : ComputablePred Q) (hsub : ∀ i, Q i → Homogeneous obs atom i) :
    ∃ verify : Certifier, Computable verify ∧ SoundCertifier obs atom verify ∧ Certified verify = Q := by
  obtain ⟨rep, hr, hrep⟩ := select_representative obs ho hs
  obtain ⟨select, hselect, hselect_eq⟩ := ComputablePred.computable_iff.mp hQ
  have hchoose (i : ℕ) : Q i ↔ select i = true := Iff.of_eq (congrFun hselect_eq i)
  let verify : Certifier := fun a => select a.1 && (atom (rep a.1) == a.2.1)
  have hbit : Computable fun a : ℕ × (Bool × ℕ) => atom (rep a.1) == a.2.1 :=
    (Primrec.beq (α := Bool)).to_comp.comp ((ha.comp hr).comp Computable.fst)
      (Computable.fst.comp Computable.snd)
  have hv : Computable verify := Primrec.and.to_comp.comp (hselect.comp Computable.fst) hbit
  have htest (i : ℕ) (b : Bool) (w : ℕ) : verify (i, (b, w)) = true ↔
      Q i ∧ atom (rep i) = b := by
    simp [verify, hchoose]
  refine ⟨verify, hv, ?_, ?_⟩
  · intro s b w hw
    obtain ⟨hq, hb⟩ := (htest (obs s) b w).mp hw
    exact (hsub _ hq s (rep (obs s)) rfl (hrep (obs s))).trans hb
  · funext i
    apply propext
    exact ⟨fun ⟨b, w, hw⟩ => ((htest i b w).mp hw).1,
      fun hi => ⟨atom (rep i), 0, (htest _ _ _).mpr ⟨hi, rfl⟩⟩⟩

/-- With realized observations, decidability is exactly complete sound certification. -/
theorem complete_certifier_iff_decidable (obs : ℕ → ℕ) (atom : ℕ → Bool)
    (ho : Computable obs) (ha : Computable atom) (hs : Function.Surjective obs) :
    (∃ verify : Certifier, Computable verify ∧ SoundCertifier obs atom verify ∧
      Certified verify = Homogeneous obs atom) ↔ ComputablePred (Homogeneous obs atom) := by
  constructor
  · rintro ⟨verify, hv, _, heq⟩
    exact ComputablePred.computable_iff_re_compl_re'.2
      ⟨heq ▸ computable_certified_re verify hv, ambiguity_re obs atom ho ha⟩
  · intro hQ
    exact exact_domain_certifier obs atom ho ha hs hQ (fun _ => id)

private theorem finite_domain_computable (s : Finset ℕ) :
    ComputablePred fun i => i ∈ s := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨_, Computable.const false⟩
  | @insert e s _ ih =>
    obtain ⟨f, hf, hiff⟩ := ComputablePred.computable_iff.mp ih
    have hbeq : Computable fun i : ℕ => i == e :=
      (Primrec.beq (α := ℕ)).to_comp.comp Computable.id (Computable.const e)
    refine ComputablePred.computable_iff.mpr
      ⟨fun i => (i == e) || f i, Primrec.or.to_comp.comp hbeq hf, ?_⟩
    funext i
    apply propext
    simp [hiff]

/-- Every finite subdomain of homogeneous observations admits a sound verifier. -/
theorem finite_sound_certifier (obs : ℕ → ℕ) (atom : ℕ → Bool)
    (ho : Computable obs) (ha : Computable atom) (hs : Function.Surjective obs)
    (s : Finset ℕ) (hsub : ∀ i ∈ s, Homogeneous obs atom i) :
    ∃ verify : Certifier, Computable verify ∧ SoundCertifier obs atom verify ∧
      Certified verify = (fun i => i ∈ s) :=
  exact_domain_certifier obs atom ho ha hs (finite_domain_computable s) hsub

def SoundCoverages (obs : ℕ → ℕ) (atom : ℕ → Bool) (p : ℕ → ℝ≥0∞) :
    Set ℝ≥0∞ :=
  {c | ∃ verify : Certifier, Computable verify ∧ SoundCertifier obs atom verify ∧
    c = mass p (Certified verify)}

/-- The sound coverage supremum equals the semantic mass, regardless of weight computability. -/
theorem semantic_mass_is_coverage_supremum (obs : ℕ → ℕ) (atom : ℕ → Bool)
    (ho : Computable obs) (ha : Computable atom) (hs : Function.Surjective obs)
    (p : ℕ → ℝ≥0∞) :
    IsLUB (SoundCoverages obs atom p) (mass p (Homogeneous obs atom)) := by
  classical
  constructor
  · rintro c ⟨verify, _, sound, rfl⟩
    apply mass_mono
    intro i hi
    exact domain_subset_homogeneous obs atom sound hi
  · intro c hc
    unfold mass
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro s
    let f := s.filter (Homogeneous obs atom)
    obtain ⟨verify, hv, sound, hdom⟩ := finite_sound_certifier obs atom ho ha hs f
      (fun i hi => (Finset.mem_filter.mp hi).2)
    have hmass : mass p (Certified verify) = ∑ i ∈ f, p i := by
      rw [hdom, mass, tsum_eq_sum (s := f)]
      · exact Finset.sum_congr rfl (fun i hi => if_pos hi)
      · intro i hi
        exact if_neg hi
    have hfc : ∑ i ∈ f, p i ≤ c := by
      rw [← hmass]
      exact hc ⟨verify, hv, sound, rfl⟩
    simpa [f, Finset.sum_filter] using hfc

/-- The semantic mass is attained precisely when its knowability domain is decidable. -/
theorem semantic_ceiling_attainment_iff_decidable (obs : ℕ → ℕ) (atom : ℕ → Bool)
    (ho : Computable obs) (ha : Computable atom) (hs : Function.Surjective obs)
    (p : ℕ → ℝ≥0∞) (hfin : (∑' i, p i) ≠ ⊤) (hpos : ∀ i, 0 < p i) :
    mass p (Homogeneous obs atom) ∈ SoundCoverages obs atom p ↔
      ComputablePred (Homogeneous obs atom) := by
  rw [← complete_certifier_iff_decidable obs atom ho ha hs]
  constructor
  · rintro ⟨verify, hv, sound, heq⟩
    exact ⟨verify, hv, sound,
      (mass_eq_iff_predicates p hfin hpos
        (fun _ hi => domain_subset_homogeneous obs atom sound hi)).mp heq.symm⟩
  · rintro ⟨verify, hv, sound, heq⟩
    exact ⟨verify, hv, sound, congrArg (mass p) heq.symm⟩

abbrev CertifierFamily := ℕ × (ℕ × (Bool × ℕ)) → Bool

def familyMember (verify : CertifierFamily) (j : ℕ) : Certifier :=
  fun a => verify (j, a)

def familyUnion (verify : CertifierFamily) : Certifier :=
  fun a => verify (a.2.2.unpair.1, (a.1, (a.2.1, a.2.2.unpair.2)))

private theorem familyUnion_computable (verify : CertifierFamily) (hv : Computable verify) :
    Computable (familyUnion verify) := by
  open Computable in
  have hpair : Computable fun a : ℕ × (Bool × ℕ) => a.2.2.unpair :=
    unpair.comp (snd.comp snd)
  exact hv.comp ((fst.comp hpair).pair
    (fst.pair ((fst.comp snd).pair (snd.comp hpair))))

/-- A uniform family with semantic mass as its coverage supremum attains it in its tagged union. -/
theorem semantic_ceiling_uniform_iff_decidable (obs : ℕ → ℕ) (atom : ℕ → Bool)
    (ho : Computable obs) (ha : Computable atom) (hs : Function.Surjective obs)
    (p : ℕ → ℝ≥0∞) (hfin : (∑' i, p i) ≠ ⊤) (hpos : ∀ i, 0 < p i) :
    (∃ verify : CertifierFamily, Computable verify ∧
      (∀ j, SoundCertifier obs atom (familyMember verify j)) ∧
      (⨆ j, mass p (Certified (familyMember verify j))) = mass p (Homogeneous obs atom)) ↔
      ComputablePred (Homogeneous obs atom) := by
  rw [← semantic_ceiling_attainment_iff_decidable obs atom ho ha hs p hfin hpos]
  constructor
  · rintro ⟨verify, hv, hsound, hsup⟩
    have hUsound : SoundCertifier obs atom (familyUnion verify) := by
      intro s b w hw
      exact hsound w.unpair.1 s b w.unpair.2 hw
    have hle (j : ℕ) :
        mass p (Certified (familyMember verify j)) ≤ mass p (Certified (familyUnion verify)) := by
      apply mass_mono
      rintro i ⟨b, w, hw⟩
      exact ⟨b, Nat.pair j w, by simpa [familyUnion, familyMember] using hw⟩
    have ht : mass p (Homogeneous obs atom) ≤ mass p (Certified (familyUnion verify)) :=
      hsup ▸ iSup_le hle
    have hb : mass p (Certified (familyUnion verify)) ≤ mass p (Homogeneous obs atom) :=
      mass_mono p (fun _ hi => domain_subset_homogeneous obs atom hUsound hi)
    exact ⟨familyUnion verify, familyUnion_computable verify hv, hUsound, le_antisymm ht hb⟩
  · rintro ⟨verify, hv, hsound, heq⟩
    let family : CertifierFamily := fun a => verify a.2
    refine ⟨family, hv.comp Computable.snd, fun _ => hsound, ?_⟩
    change (⨆ _ : ℕ, mass p (Certified verify)) = mass p (Homogeneous obs atom)
    rw [ciSup_const]
    exact heq.symm

def SoundReader (obs : ℕ → ℕ) (atom : ℕ → Bool) (reader : ℕ → Option Bool) : Prop :=
  ∀ s b, reader (obs s) = some b → atom s = b

theorem strict_ignorance_iff_no_sound_reader (obs : ℕ → ℕ) (atom : ℕ → Bool) (s : ℕ) :
    EpistemicModal.Ignorant obs (fun t => atom t = true) s ↔
      ∀ reader : ℕ → Option Bool, Computable reader → SoundReader obs atom reader →
        reader (obs s) = none := by
  classical
  constructor
  · intro h reader _ sound
    obtain ⟨pos, neg, hp, hn, hp', hn'⟩ :=
      (EpistemicModal.ignorant_iff_mixed_fiber obs (fun t => atom t = true) s).mp h
    cases hr : reader (obs s) with
    | none => rfl
    | some b =>
      have hpos := sound pos b (hp ▸ hr)
      have hneg := sound neg b (hn ▸ hr)
      exact (hn' (hneg.trans (hpos.symm.trans hp'))).elim
  · intro h
    by_contra hi
    have hhom : Homogeneous obs atom (obs s) := by
      intro a b hoa hob
      cases ha : atom a <;> cases hb : atom b
      · rfl
      · exact (hi ((EpistemicModal.ignorant_iff_mixed_fiber obs
          (fun t => atom t = true) s).mpr ⟨b, a, hob, hoa, hb, by simp [ha]⟩)).elim
      · exact (hi ((EpistemicModal.ignorant_iff_mixed_fiber obs
          (fun t => atom t = true) s).mpr ⟨a, b, hoa, hob, ha, by simp [hb]⟩)).elim
      · rfl
    let reader (i : ℕ) := cond (i == obs s) (some (atom s)) none
    have hreader : Computable reader :=
      Computable.cond ((Primrec.beq (α := ℕ)).to_comp.comp Computable.id (Computable.const (obs s)))
        (Computable.const (some (atom s))) (Computable.const none)
    have hs : SoundReader obs atom reader := by
      intro t b hr
      by_cases he : obs t = obs s
      · exact (hhom t s he rfl).trans (by simpa [reader, he] using hr)
      · have hf : (obs t == obs s) = false := by simpa using he
        simp [reader, hf] at hr
    have habstain := h reader hreader hs
    simp [reader] at habstain

/-- A cross-view attribution amounts to forced abstention of every sound effective reader. -/
theorem coarse_knows_ignorance_iff_forced_abstention
    (coarse fine : ℕ → ℕ) (atom : ℕ → Bool) (s : ℕ) :
    EpistemicModal.Knows coarse (EpistemicModal.Ignorant fine (fun t => atom t = true)) s ↔
      ∀ reader : ℕ → Option Bool, Computable reader → SoundReader fine atom reader →
        ∀ t, coarse t = coarse s → reader (fine t) = none := by
  constructor
  · intro h reader hr hs t ht
    exact (strict_ignorance_iff_no_sound_reader fine atom t).mp (h t ht) reader hr hs
  · intro h t ht
    exact (strict_ignorance_iff_no_sound_reader fine atom t).mpr (fun reader hr hs => h reader hr hs t ht)

#print axioms complete_certifier_iff_decidable
#print axioms finite_sound_certifier
#print axioms semantic_mass_is_coverage_supremum
#print axioms semantic_ceiling_attainment_iff_decidable
#print axioms semantic_ceiling_uniform_iff_decidable
#print axioms coarse_knows_ignorance_iff_forced_abstention

end EpistemicAuditBridge
