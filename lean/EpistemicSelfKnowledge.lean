import Mathlib.Computability.Halting
import Mathlib.Algebra.Order.Field.Rat

namespace EpistemicSelfKnowledge

variable {S I : Type*}

def FiberConstant (observe : S → I) (truth : S → Bool) : Prop :=
  ∀ s t, observe s = observe t → truth s = truth t

theorem observable_iff (observe : S → I) (truth : S → Bool) :
    FiberConstant observe truth ↔ ∃ readout : I → Bool, ∀ s, readout (observe s) = truth s := by
  classical
  constructor
  · intro hf
    let readout := fun i => if ∃ s, observe s = i ∧ truth s = true then true else false
    refine ⟨readout, ?_⟩
    intro s
    unfold readout
    cases hs : truth s
    · apply if_neg
      rintro ⟨t, ht, ht'⟩
      have hh := hf t s ht
      simp [hs, ht'] at hh
    · exact if_pos ⟨s, rfl, hs⟩
  · rintro ⟨readout, hr⟩ s t h
    rw [← hr s, ← hr t, h]

theorem effective_readout_iff_separator [Primcodable I] (observe : S → I)
    (truth : S → Bool) :
    (∃ d : I → Bool, Computable d ∧ ∀ s, d (observe s) = truth s) ↔
      ∃ separates : I → Prop, ComputablePred separates ∧
        ∀ s, separates (observe s) ↔ truth s = true := by
  constructor
  · rintro ⟨d, hd, correct⟩
    exact ⟨fun i => d i = true, ComputablePred.computable_iff.mpr ⟨d, hd, rfl⟩,
      fun s => by change d (observe s) = true ↔ truth s = true; rw [correct s]⟩
  · rintro ⟨separates, hc, hs⟩
    obtain ⟨d, hd, hdef⟩ := ComputablePred.computable_iff.mp hc
    refine ⟨d, hd, fun s => ?_⟩
    have heq := hs s
    rw [hdef] at heq
    cases h₁ : d (observe s) <;> cases h₂ : truth s <;> simp_all

def Sound (observe : S → I) (truth : S → Bool) (judge : I → Option Bool) : Prop :=
  ∀ s b, judge (observe s) = some b → truth s = b

theorem sound_answers_constant_on_fiber {observe : S → I} {truth : S → Bool}
    {judge : I → Option Bool} (h : Sound observe truth judge)
    {s t : S} {b : Bool} (hobs : observe s = observe t)
    (hanswer : judge (observe s) = some b) : truth s = truth t := by
  exact (h s b hanswer).trans (h t b (hobs ▸ hanswer)).symm

theorem bounded_certificate_sound (truth : I → Bool) (verify : I → Bool → ℕ → Bool)
    (hv : ∀ i b w, verify i b w = true → truth i = b)
    {judge : I → Option Bool}
    (h : ∀ i b, judge i = some b → ∃ w, verify i b w = true) : Sound id truth judge := by
  intro i b hb
  obtain ⟨w, hw⟩ := h i b hb
  exact hv i b w hw

section Atomic

variable {A T : Type*} (weight : A → ℚ) (loss : T → ℚ)
variable (tolerance : ℕ → ℚ) (precision : A → ℕ)

theorem exact_readout_of_small_loss (f : T → A → Bool) (truth : A → Bool)
    (hsmall : ∀ a, tolerance (precision a) ≤ weight a)
    (hatom : ∀ t a, f t a ≠ truth a → weight a ≤ loss t)
    (m : ℕ → T) (hm : ∀ k, loss (m k) < tolerance k) :
    ∀ a, f (m (precision a)) a = truth a := by
  intro a
  by_contra hne
  exact (not_lt_of_ge ((hsmall a).trans (hatom _ a hne))) (hm _)

theorem exact_domain_of_small_residual (seen : T → A → Bool) (eventual : A → Prop)
    (hsmall : ∀ a, tolerance (precision a) ≤ weight a)
    (hseen : ∀ t a, seen t a = true → eventual a)
    (hatom : ∀ t a, eventual a → seen t a ≠ true → weight a ≤ loss t)
    (m : ℕ → T) (hm : ∀ k, loss (m k) < tolerance k) :
    ∀ a, eventual a ↔ seen (m (precision a)) a = true := by
  intro a
  refine ⟨fun he => ?_, hseen _ a⟩
  by_contra hn
  exact (not_lt_of_ge ((hsmall a).trans (hatom _ a he hn))) (hm _)

end Atomic

open Nat.Partrec (Code)
open Nat.Partrec.Code

def Halts (c : Code) : Prop := (eval c 0).Dom

def HaltsBy (p : ℕ × Code) : Bool := (evaln p.1 p.2 0).isSome

theorem haltsBy_computable : Computable HaltsBy :=
  (Primrec.option_isSome.comp
    (evaln_prim.comp (Primrec.id.pair (Primrec.const 0)))).to_comp

theorem haltsBy_sound (t : ℕ) (c : Code) (h : HaltsBy (t, c) = true) : Halts c := by
  cases he : evaln t c 0 with
  | none => simp [HaltsBy, he] at h
  | some x => exact Part.dom_iff_mem.mpr ⟨x, evaln_sound (k := t) (by simp [he])⟩

theorem haltsBy_eventually_complete (c : Code) :
    Halts c ↔ ∃ t, HaltsBy (t, c) = true := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
    obtain ⟨t, ht⟩ := evaln_complete.mp hx
    have he : evaln t c 0 = some x := by simpa using ht
    exact ⟨t, by simp [HaltsBy, he]⟩
  · rintro ⟨t, ht⟩
    exact haltsBy_sound t c ht

theorem no_halting_readout (d : Code → Bool) (hd : Computable d)
    (hcorrect : ∀ c, Halts c ↔ d c = true) : False := by
  apply ComputablePred.halting_problem 0
  exact ComputablePred.computable_iff.mpr
    ⟨d, hd, funext fun c => propext (hcorrect c)⟩

theorem no_effective_coverage_modulus
    (seen : ℕ × Code → Bool) (hs : Computable seen)
    (eventual : Code → Prop) (hn : ¬ComputablePred eventual)
    (weight : Code → ℚ) (gap : ℕ → ℚ) (tol : ℕ → ℚ) (precision : Code → ℕ)
    (hp : Computable precision)
    (hsmall : ∀ c, tol (precision c) ≤ weight c)
    (hseen : ∀ t c, seen (t, c) = true → eventual c)
    (hatom : ∀ t c, eventual c → seen (t, c) ≠ true → weight c ≤ gap t)
    (m : ℕ → ℕ) (hm : Computable m) (hgap : ∀ k, gap (m k) < tol k) : False := by
  apply hn
  refine ComputablePred.computable_iff.mpr ⟨fun c => seen (m (precision c), c), ?_, ?_⟩
  · exact hs.comp ((hm.comp hp).pair Computable.id)
  · apply funext
    intro c
    apply propext
    exact exact_domain_of_small_residual weight gap tol precision
      (fun t a => seen (t, a)) eventual hsmall hseen hatom m hgap c

theorem no_effective_halting_error_modulus
    (guess : ℕ × Code → Bool) (hg : Computable guess)
    (weight : Code → ℚ) (risk : ℕ → ℚ) (tol : ℕ → ℚ) (precision : Code → ℕ)
    (hp : Computable precision)
    (hsmall : ∀ c, tol (precision c) ≤ weight c)
    (hatom : ∀ t c, ¬(Halts c ↔ guess (t, c) = true) → weight c ≤ risk t)
    (m : ℕ → ℕ) (hm : Computable m) (hrisk : ∀ k, risk (m k) < tol k) : False := by
  apply no_halting_readout (fun c => guess (m (precision c), c))
    (hg.comp ((hm.comp hp).pair Computable.id))
  intro c
  by_contra h
  exact (not_lt_of_ge ((hsmall c).trans (hatom _ _ h))) (hrisk _)

theorem every_negative_verifier_misses_a_nonhalting_code
    (accept : Code × ℕ → Bool) (ha : Computable accept)
    (hsound : ∀ c w, accept (c, w) = true → ¬ Halts c) :
    ∃ c, ¬ Halts c ∧ ∀ w, accept (c, w) ≠ true := by
  let wait : Code → ℕ → Part ℕ :=
    fun c _ => Nat.rfind (fun w => Part.some (accept (c, w)))
  have hstep : Partrec (fun p : Code × ℕ => Part.some (accept p)) := ha
  have hsearch : Partrec fun c => Nat.rfind (fun w => Part.some (accept (c, w))) :=
    Partrec.rfind hstep.to₂
  have hwait : Partrec₂ wait := (hsearch.comp Computable.fst).to₂
  obtain ⟨c, hc⟩ := fixed_point₂ hwait
  have hdom : Halts c ↔ ∃ w, accept (c, w) = true := by
    unfold Halts
    rw [hc]
    simp [wait, Nat.rfind_dom]
  have hn : ∀ w, accept (c, w) ≠ true := fun w hw => hsound c w hw (hdom.mpr ⟨w, hw⟩)
  exact ⟨c, fun h => by obtain ⟨w, hw⟩ := hdom.mp h; exact hn w hw, hn⟩

theorem jointly_computable_negative_verifiers_miss_one_code
    (accept : ℕ × (Code × ℕ) → Bool) (ha : Computable accept)
    (hsound : ∀ j c w, accept (j, (c, w)) = true → ¬ Halts c) :
    ∃ c, ¬ Halts c ∧ ∀ j w, accept (j, (c, w)) ≠ true := by
  let combine : Code × ℕ → Bool :=
    fun p => accept (p.2.unpair.1, (p.1, p.2.unpair.2))
  have hup : Computable fun p : Code × ℕ => p.2.unpair :=
    Computable.unpair.comp Computable.snd
  have hc : Computable combine := ha.comp
    ((Computable.fst.comp hup).pair (Computable.fst.pair (Computable.snd.comp hup)))
  obtain ⟨c, hn, hmiss⟩ := every_negative_verifier_misses_a_nonhalting_code
    combine hc (fun c w h => hsound w.unpair.1 c w.unpair.2 h)
  refine ⟨c, hn, fun j w h => hmiss (Nat.pair j w) ?_⟩
  simpa [combine, Nat.unpair_pair] using h

#print axioms observable_iff
#print axioms effective_readout_iff_separator
#print axioms sound_answers_constant_on_fiber
#print axioms bounded_certificate_sound
#print axioms exact_readout_of_small_loss
#print axioms exact_domain_of_small_residual
#print axioms haltsBy_computable
#print axioms haltsBy_sound
#print axioms haltsBy_eventually_complete
#print axioms no_halting_readout
#print axioms no_effective_coverage_modulus
#print axioms no_effective_halting_error_modulus
#print axioms every_negative_verifier_misses_a_nonhalting_code
#print axioms jointly_computable_negative_verifiers_miss_one_code

end EpistemicSelfKnowledge
