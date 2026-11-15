import Mathlib.Computability.Halting
import Mathlib.Data.Nat.Find

namespace EpistemicModal

/-- Same-view knowledge in an interpreted system. -/
def Knows {S I : Type*} (obs : S → I) (p : S → Prop) (s : S) : Prop :=
  ∀ t, obs t = obs s → p t

/-- Strict ignorance is failure to know either polarity. -/
def Ignorant {S I : Type*} (obs : S → I) (p : S → Prop) (s : S) : Prop :=
  ¬ Knows obs p s ∧ ¬ Knows obs (fun t => ¬ p t) s

section SameView

variable {S I J : Type*} (obs : S → I) (p : S → Prop) (s : S)

theorem knows_iff_of_eq {s t : S} (h : obs s = obs t) :
    Knows obs p s ↔ Knows obs p t := by
  unfold Knows
  rw [h]

theorem knows_factive : Knows obs p s → p s :=
  fun h => h s rfl

theorem knows_knows_iff : Knows obs (Knows obs p) s ↔ Knows obs p s := by
  constructor
  · exact knows_factive obs (Knows obs p) s
  · intro h t ht
    exact (knows_iff_of_eq obs p ht).2 h

theorem knows_not_knows_iff :
    Knows obs (fun t => ¬ Knows obs p t) s ↔ ¬ Knows obs p s := by
  constructor
  · exact knows_factive obs (fun t => ¬ Knows obs p t) s
  · intro h t ht hkt
    exact h ((knows_iff_of_eq obs p ht).1 hkt)

theorem knows_refined_knows_iff (fine : S → J)
    (refines : ∀ {x y}, fine x = fine y → obs x = obs y) :
    Knows obs (Knows fine p) s ↔ Knows obs p s := by
  constructor
  · intro h t ht
    exact knows_factive fine p t (h t ht)
  · intro h t ht u hu
    exact h u ((refines hu).trans ht)

theorem refined_knows_knows_iff (fine : S → J)
    (refines : ∀ {x y}, fine x = fine y → obs x = obs y) :
    Knows fine (Knows obs p) s ↔ Knows obs p s := by
  constructor
  · exact knows_factive fine (Knows obs p) s
  · intro h t ht
    exact (knows_iff_of_eq obs p (refines ht)).2 h

theorem ignorant_iff_mixed_fiber :
    Ignorant obs p s ↔
      ∃ pos neg, obs pos = obs s ∧ obs neg = obs s ∧ p pos ∧ ¬ p neg := by
  classical
  unfold Ignorant Knows
  push_neg
  constructor
  · rintro ⟨⟨neg, hn, hpn⟩, ⟨pos, hp, hpp⟩⟩
    exact ⟨pos, neg, hp, hn, Classical.byContradiction hpp, hpn⟩
  · rintro ⟨pos, neg, hp, hn, hpp, hpn⟩
    exact ⟨⟨neg, hn, hpn⟩, ⟨pos, hp, fun h => h hpp⟩⟩

theorem knows_fine_ignorance_implies_coarse_ignorance (fine : S → J)
    (refines : ∀ {x y}, fine x = fine y → obs x = obs y)
    (h : Knows obs (Ignorant fine p) s) : Ignorant obs p s := by
  obtain ⟨pos, neg, hp, hn, hpp, hpn⟩ :=
    (ignorant_iff_mixed_fiber fine p s).1 (h s rfl)
  exact (ignorant_iff_mixed_fiber obs p s).2
    ⟨pos, neg, refines hp, refines hn, hpp, hpn⟩

end SameView

section Representation

variable (R : ℕ → ℕ → ℕ → Prop)

def FirstWitness (e x t : ℕ) : Prop :=
  R e x t ∧ ∀ i : Fin t, ¬ R e x i

instance [DecidableRel (R e)] (x t : ℕ) : Decidable (FirstWitness R e x t) :=
  inferInstanceAs (Decidable (R e x t ∧ ∀ i : Fin t, ¬ R e x i))

def Admissible (e x : ℕ) : ℕ → Prop
  | 0 => True
  | t + 1 => FirstWitness R e x t

instance [DecidableRel (R e)] (x z : ℕ) : Decidable (Admissible R e x z) := by
  cases z with
  | zero => exact inferInstanceAs (Decidable True)
  | succ t => exact inferInstanceAs (Decidable (FirstWitness R e x t))

structure World where
  program : ℕ
  localView : ℕ
  mode : ℕ
  admissible : Admissible R program localView mode

def anchor (e x : ℕ) : World R := ⟨e, x, 0, trivial⟩

def coarse (s : World R) : ℕ := s.program

def fine (s : World R) : ℕ × ℕ := (s.program, s.localView)

def atom (s : World R) : Prop := s.mode = 0

theorem fine_refines_coarse {s t : World R} (h : fine R s = fine R t) :
    coarse R s = coarse R t :=
  congrArg Prod.fst h

theorem firstWitness_unique {e x t u : ℕ}
    (ht : FirstWitness R e x t) (hu : FirstWitness R e x u) : t = u := by
  rcases lt_trichotomy t u with h | h | h
  · exact (hu.2 ⟨t, h⟩ ht.1).elim
  · exact h
  · exact (ht.2 ⟨u, h⟩ hu.1).elim

theorem firstWitness_exists {e x : ℕ} [DecidablePred (R e x)]
    (h : ∃ t, R e x t) : ∃ t, FirstWitness R e x t := by
  exact ⟨Nat.find h, Nat.find_spec h, fun i => Nat.find_min h i.isLt⟩

theorem fine_nonanchors_unique {s t : World R} (h : fine R s = fine R t)
    (hs : ¬ atom R s) (ht : ¬ atom R t) : s = t := by
  cases s with
  | mk e x z hz =>
    cases t with
    | mk e' x' z' hz' =>
      have he : e = e' := congrArg Prod.fst h
      have hx : x = x' := congrArg Prod.snd h
      subst e'
      subst x'
      cases z with
      | zero => exact (hs rfl).elim
      | succ u =>
        cases z' with
        | zero => exact (ht rfl).elim
        | succ v =>
          have huv := firstWitness_unique R hz hz'
          subst v
          rfl

theorem anchor_unique {s : World R} (h : atom R s) :
    s = anchor R s.program s.localView := by
  cases s with
  | mk e x z hz =>
    change z = 0 at h
    subst z
    rfl

theorem fine_ignorance_iff (s : World R) :
    Ignorant (fine R) (atom R) s ↔ ∃ t, R s.program s.localView t := by
  classical
  constructor
  · intro h
    obtain ⟨_, neg, _, hn, _, hneg⟩ :=
      (ignorant_iff_mixed_fiber (fine R) (atom R) s).1 h
    have he : neg.program = s.program := congrArg Prod.fst hn
    have hx : neg.localView = s.localView := congrArg Prod.snd hn
    have ha := neg.admissible
    cases hm : neg.mode with
    | zero => exact (hneg hm).elim
    | succ t =>
      rw [hm] at ha
      exact ⟨t, he ▸ hx ▸ ha.1⟩
  · intro h
    obtain ⟨t, ht⟩ := firstWitness_exists R h
    let neg : World R := ⟨s.program, s.localView, t + 1, ht⟩
    apply (ignorant_iff_mixed_fiber (fine R) (atom R) s).2
    refine ⟨anchor R s.program s.localView, neg, rfl, rfl, rfl, ?_⟩
    exact Nat.succ_ne_zero t

theorem coarse_knows_fine_ignorance_iff (s : World R) :
    Knows (coarse R) (Ignorant (fine R) (atom R)) s ↔
      ∀ x, ∃ t, R s.program x t := by
  constructor
  · intro h x
    exact (fine_ignorance_iff R (anchor R s.program x)).1 (h _ rfl)
  · intro h t ht
    have he : t.program = s.program := ht
    apply (fine_ignorance_iff R t).2
    rw [he]
    exact h t.localView

end Representation

section MachineModel

open Denumerable Nat.Partrec Nat.Partrec.Code

def boundedHalting (e x t : ℕ) : Prop := (evaln t (ofNat Code e) x).isSome

instance (e x t : ℕ) : Decidable (boundedHalting e x t) :=
  inferInstanceAs (Decidable ((evaln t (ofNat Code e) x).isSome : Prop))

theorem boundedHalting_computable :
    ComputablePred (fun e : ℕ × ℕ × ℕ => boundedHalting e.1 e.2.1 e.2.2) := by
  refine ComputablePred.computable_iff.mpr ⟨_, ?_, rfl⟩
  exact Primrec.option_isSome.to_comp.comp
    (evaln_prim.to_comp.comp
      (((Computable.snd.comp Computable.snd).pair
        ((Computable.ofNat Code).comp Computable.fst)).pair (Computable.fst.comp Computable.snd)))

theorem boundedHalting_iff_eval_dom (e x : ℕ) :
    (∃ t, boundedHalting e x t) ↔ (eval (ofNat Code e) x).Dom := by
  constructor
  · rintro ⟨t, ht⟩
    cases hv : evaln t (ofNat Code e) x with
    | none => simp [boundedHalting, hv] at ht
    | some z =>
      exact Part.dom_iff_mem.mpr ⟨z, evaln_sound (k := t) (by simpa using hv)⟩
  · intro h
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp h
    obtain ⟨t, ht⟩ := evaln_complete.mp hz
    have hv : evaln t (ofNat Code e) x = some z := by simpa using ht
    exact ⟨t, by simp [boundedHalting, hv]⟩

theorem coarse_ignorance_judgment_iff_total (e : ℕ) :
    Knows (coarse boundedHalting) (Ignorant (fine boundedHalting) (atom boundedHalting))
      (anchor boundedHalting e 0) ↔ ∀ x, (eval (ofNat Code e) x).Dom := by
  rw [coarse_knows_fine_ignorance_iff]
  exact forall_congr' (fun x => boundedHalting_iff_eval_dom e x)

theorem fine_knowledge_whether_iff_nonhalting (e x : ℕ) :
    (Knows (fine boundedHalting) (atom boundedHalting) (anchor boundedHalting e x) ∨
      Knows (fine boundedHalting) (fun w => ¬ atom boundedHalting w)
        (anchor boundedHalting e x)) ↔ ¬ (eval (ofNat Code e) x).Dom := by
  classical
  rw [← boundedHalting_iff_eval_dom]
  have h : Ignorant (fine boundedHalting) (atom boundedHalting) (anchor boundedHalting e x) ↔
      ∃ t, boundedHalting e x t := fine_ignorance_iff boundedHalting _
  rw [← h]
  constructor
  · rintro (hp | hn) hu
    · exact hu.1 hp
    · exact hu.2 hn
  · intro hn
    by_cases hp : Knows (fine boundedHalting) (atom boundedHalting) (anchor boundedHalting e x)
    · exact Or.inl hp
    · exact Or.inr (Classical.byContradiction (fun hn' => hn ⟨hp, hn'⟩))

/-- Totality of the program represented by a Mathlib code. -/
def CodeTotal (c : Code) : Prop := ∀ x, (eval c x).Dom

theorem total_code_missed_by_positive_verifier (accept : Code × ℕ → Bool)
    (ha : Computable accept) (hsound : ∀ c w, accept (c,w) = true → CodeTotal c) :
    ∃ c, CodeTotal c ∧ ∀ w, accept (c,w) ≠ true := by
  let program (p : Code × ℕ) : Part ℕ :=
    if accept p then Part.none else Part.some 0
  have hprogram : Partrec program := by
    have hzero : Partrec (fun _ : Code × ℕ => Part.some (0 : ℕ)) := Computable.const 0
    exact (Partrec.cond ha Partrec.none hzero).of_eq
      (fun p => by cases h : accept p <;> simp [program, h])
  obtain ⟨c, hc⟩ := fixed_point₂ hprogram.to₂
  have hdom (w : ℕ) : (eval c w).Dom ↔ accept (c,w) = false := by
    rw [hc]
    cases h : accept (c,w) <;> simp [program, h]
  have hn (w : ℕ) : accept (c,w) ≠ true := fun hw => by
    have he := (hdom w).1 (hsound c w hw w)
    simp [hw] at he
  exact ⟨c, fun w => (hdom w).2 (Bool.eq_false_iff.2 (hn w)), hn⟩

theorem nontotal_code_missed_by_negative_verifier (accept : Code × ℕ → Bool)
    (ha : Computable accept) (hsound : ∀ c w, accept (c,w) = true → ¬ CodeTotal c) :
    ∃ c, ¬ CodeTotal c ∧ ∀ w, accept (c,w) ≠ true := by
  let search (c : Code) : Part ℕ := Nat.rfind (fun w => Part.some (accept (c,w)))
  have hstep : Partrec (fun p : Code × ℕ => Part.some (accept p)) := ha
  have hsearch : Partrec search := Partrec.rfind hstep.to₂
  obtain ⟨c, hc⟩ := fixed_point₂ (hsearch.comp Computable.fst).to₂
  have hdom (x : ℕ) : (eval c x).Dom ↔ ∃ w, accept (c,w) = true := by
    rw [hc]
    simp [search, Nat.rfind_dom]
  have hn (w : ℕ) : accept (c,w) ≠ true := fun hw =>
    hsound c w hw (fun x => (hdom x).2 ⟨w, hw⟩)
  exact ⟨c, fun ht => by obtain ⟨w, hw⟩ := (hdom 0).1 (ht 0); exact hn w hw, hn⟩

private def combineFamily (accept : ℕ × (Code × ℕ) → Bool) (p : Code × ℕ) : Bool :=
  accept (p.2.unpair.1, (p.1, p.2.unpair.2))

private theorem combineFamily_computable {accept : ℕ × (Code × ℕ) → Bool}
    (ha : Computable accept) : Computable (combineFamily accept) := by
  have hup : Computable fun p : Code × ℕ => p.2.unpair :=
    Computable.unpair.comp Computable.snd
  exact ha.comp ((Computable.fst.comp hup).pair (Computable.fst.pair (Computable.snd.comp hup)))

theorem uniform_totality_certifiers_miss_both_signs
    (yes no : ℕ × (Code × ℕ) → Bool)
    (hy : Computable yes) (hn : Computable no)
    (hys : ∀ j c w, yes (j,(c,w)) = true → CodeTotal c)
    (hns : ∀ j c w, no (j,(c,w)) = true → ¬ CodeTotal c) :
    ∃ cp cn : Code, CodeTotal cp ∧ ¬ CodeTotal cn ∧
      ∀ j w, (yes (j,(cp,w)) ≠ true ∧ no (j,(cp,w)) ≠ true) ∧
             (yes (j,(cn,w)) ≠ true ∧ no (j,(cn,w)) ≠ true) := by
  obtain ⟨cp, hcp, hcpy⟩ := total_code_missed_by_positive_verifier (combineFamily yes)
    (combineFamily_computable hy) (fun c w hw => hys w.unpair.1 c w.unpair.2 hw)
  obtain ⟨cn, hcn, hcnn⟩ := nontotal_code_missed_by_negative_verifier (combineFamily no)
    (combineFamily_computable hn) (fun c w hw => hns w.unpair.1 c w.unpair.2 hw)
  refine ⟨cp, cn, hcp, hcn, fun j w => ⟨⟨?_, fun h => hns j cp w h hcp⟩, ⟨fun h => hcn (hys j cn w h), ?_⟩⟩⟩
  · simpa [combineFamily, Nat.unpair_pair] using hcpy (Nat.pair j w)
  · simpa [combineFamily, Nat.unpair_pair] using hcnn (Nat.pair j w)

/-- A parameterized Kleene fixed point with an injective code map in Mathlib's numbering. -/
theorem injective_parameterized_fixed_point (f : Code × (ℕ × ℕ) → Part ℕ)
    (hf : Partrec f) :
    ∃ d : ℕ → Code, Computable d ∧ Function.Injective d ∧
      ∀ x y, eval (d x) y = f (d x, (x,y)) := by
  have hup : Computable (fun p : Code × ℕ => p.2.unpair) :=
    Computable.unpair.comp Computable.snd
  have hcurry : Computable (fun p : Code × ℕ => curry p.1 p.2.unpair.1) :=
    curry_prim.to_comp.comp Computable.fst (Computable.fst.comp hup)
  have hprog : Partrec (fun p : Code × ℕ => f (curry p.1 p.2.unpair.1, p.2.unpair)) :=
    hf.comp (hcurry.pair hup)
  obtain ⟨c, hc⟩ := fixed_point₂ hprog.to₂
  refine ⟨curry c, curry_prim.to_comp.comp (Computable.const c) Computable.id,
    fun _ _ eq => (curry_inj eq).2, ?_⟩
  intro x y
  rw [eval_curry]
  rw [show eval c (Nat.pair x y) = _ from congrFun hc (Nat.pair x y)]
  simp only [Nat.unpair_pair]

/-- The common uncovered domain contains a computable injection preserving totality. -/
theorem uniform_totality_certifiers_miss_injective_family
    (yes no : ℕ × (Code × ℕ) → Bool)
    (hy : Computable yes) (hn : Computable no)
    (hys : ∀ j c w, yes (j,(c,w)) = true → CodeTotal c)
    (hns : ∀ j c w, no (j,(c,w)) = true → ¬ CodeTotal c) :
    ∃ d : Code → Code, Computable d ∧ Function.Injective d ∧
      ∀ c, (CodeTotal (d c) ↔ CodeTotal c) ∧
        ∀ j w, yes (j,(d c,w)) ≠ true ∧ no (j,(d c,w)) ≠ true := by
  let wait (c : Code) : Part ℕ := Nat.rfind (fun w => Part.some (combineFamily no (c,w)))
  have hncomp := combineFamily_computable hn
  have hstep : Partrec (fun p : Code × ℕ => Part.some (combineFamily no p)) := hncomp
  have hwait : Partrec wait := Partrec.rfind hstep.to₂
  have hexec : Partrec (fun p : Code × (ℕ × ℕ) => eval (ofNat Code p.2.1) p.2.2) :=
    eval_part.comp ((Computable.ofNat Code).comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  obtain ⟨run, hrun, hr⟩ := Partrec.merge' hexec (hwait.comp Computable.fst)
  let cut (p : Code × (ℕ × ℕ)) : Bool := combineFamily yes (p.1,p.2.2)
  have hcut : Computable cut :=
    (combineFamily_computable hy).comp (Computable.fst.pair (Computable.snd.comp Computable.snd))
  let f (p : Code × (ℕ × ℕ)) : Part ℕ := cond (cut p) Part.none (run p)
  have hf : Partrec f := Partrec.cond hcut Partrec.none hrun
  obtain ⟨d, hd, hi, hfix⟩ := injective_parameterized_fixed_point f hf
  refine ⟨fun c => d (Encodable.encode c), hd.comp Computable.encode,
    fun _ _ h => Encodable.encode_injective (hi h), ?_⟩
  intro c
  let c' := d (Encodable.encode c)
  change (CodeTotal c' ↔ CodeTotal c) ∧ ∀ j w,
    yes (j,(c',w)) ≠ true ∧ no (j,(c',w)) ≠ true
  have hdom (y : ℕ) : (eval c' y).Dom ↔
      combineFamily yes (c',y) = false ∧
        ((eval c y).Dom ∨ ∃ w, combineFamily no (c',w) = true) := by
    change (eval (d (Encodable.encode c)) y).Dom ↔ _
    rw [hfix]
    change (cond (combineFamily yes (c',y)) Part.none (run (c', (Encodable.encode c,y)))).Dom ↔ _
    cases hc : combineFamily yes (c',y) with
    | false =>
      simpa [wait, Nat.rfind_dom, Denumerable.ofNat_encode, hc] using
        (hr (c', (Encodable.encode c,y))).2
    | true => simp [hc]
  have hpos (w : ℕ) : combineFamily yes (c',w) ≠ true := fun hw => by
    have hct := hys w.unpair.1 c' w.unpair.2 hw w
    have hh := ((hdom w).1 hct).1
    simp [hw] at hh
  have hneg (w : ℕ) : combineFamily no (c',w) ≠ true := fun hw =>
    hns w.unpair.1 c' w.unpair.2 hw
      (fun x => (hdom x).2 ⟨Bool.eq_false_iff.2 (hpos x), Or.inr ⟨w,hw⟩⟩)
  refine ⟨⟨?_, ?_⟩, fun j w => ⟨?_, ?_⟩⟩
  · intro ht y
    rcases ((hdom y).1 (ht y)).2 with h | ⟨w, hw⟩
    · exact h
    · exact (hneg w hw).elim
  · exact fun ht y => (hdom y).2 ⟨Bool.eq_false_iff.2 (hpos y), Or.inl (ht y)⟩
  · simpa [combineFamily, Nat.unpair_pair] using hpos (Nat.pair j w)
  · simpa [combineFamily, Nat.unpair_pair] using hneg (Nat.pair j w)

end MachineModel

#print axioms knows_knows_iff
#print axioms knows_not_knows_iff
#print axioms knows_refined_knows_iff
#print axioms refined_knows_knows_iff
#print axioms ignorant_iff_mixed_fiber
#print axioms knows_fine_ignorance_implies_coarse_ignorance
#print axioms firstWitness_unique
#print axioms firstWitness_exists
#print axioms fine_nonanchors_unique
#print axioms anchor_unique
#print axioms fine_ignorance_iff
#print axioms coarse_knows_fine_ignorance_iff
#print axioms boundedHalting_computable
#print axioms boundedHalting_iff_eval_dom
#print axioms coarse_ignorance_judgment_iff_total
#print axioms fine_knowledge_whether_iff_nonhalting
#print axioms total_code_missed_by_positive_verifier
#print axioms nontotal_code_missed_by_negative_verifier
#print axioms uniform_totality_certifiers_miss_both_signs
#print axioms injective_parameterized_fixed_point
#print axioms uniform_totality_certifiers_miss_injective_family

end EpistemicModal
