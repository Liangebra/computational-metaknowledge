import EpistemicSelfKnowledge
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Atomic coverage for a uniformly decidable increasing exhaustion. The gap is a
genuine infinite sum of missing weights, not an assumed atom lower bound.
-/

namespace EpistemicSelfKnowledge.CoverageMeasure

open scoped ENNReal BigOperators
open Filter

variable {A : Type*}

/-- Probability mass of a predicate for a discrete law. -/
noncomputable def mass (p : A → ℝ≥0∞) (covered : A → Prop) : ℝ≥0∞ := by
  classical
  exact ∑' e, if covered e then p e else 0

/-- The mass of the queries seen by some stage and absent from the given stage. -/
noncomputable def gap (p : A → ℝ≥0∞) (seen : ℕ × A → Bool) (t : ℕ) : ℝ≥0∞ :=
  mass p (fun e => (∃ s, seen (s, e) = true) ∧ seen (t, e) ≠ true)

theorem mass_mono (p : A → ℝ≥0∞) {B C : A → Prop}
    (h : ∀ e, B e → C e) : mass p B ≤ mass p C := by
  classical
  apply ENNReal.tsum_le_tsum
  intro e
  by_cases hb : B e
  · simp [hb, h e hb]
  · simp [hb]

theorem atom_le_mass (p : A → ℝ≥0∞) {B : A → Prop} (e : A) (he : B e) :
    p e ≤ mass p B := by
  classical
  unfold mass
  simpa only [if_pos he] using
    (ENNReal.le_tsum (f := fun i => if B i then p i else 0) e)

/-- Equality of nested masses forces equality on every positive atom. -/
theorem mass_eq_iff_agree_on_support (p : A → ℝ≥0∞) (hfin : (∑' e, p e) ≠ ⊤)
    {B C : A → Prop} (hsub : ∀ e, B e → C e) :
    mass p B = mass p C ↔ ∀ e, 0 < p e → (B e ↔ C e) := by
  classical
  let missing : A → Prop := fun e => C e ∧ ¬ B e
  have hBfin : mass p B ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfin
    have h := mass_mono p (B := B) (C := fun _ => True) (fun _ _ => trivial)
    simpa only [mass, if_true] using h
  have hsplit : mass p B + mass p missing = mass p C := by
    unfold mass
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro e
    by_cases hb : B e
    · simp [missing, hb, hsub e hb]
    · by_cases hc : C e <;> simp [missing, hb, hc]
  constructor
  · intro heq e hp
    refine ⟨hsub e, fun hc => ?_⟩
    by_contra hb
    have ha := atom_le_mass p (B := missing) e ⟨hc, hb⟩
    have hz : mass p missing = 0 := (ENNReal.add_right_inj hBfin).mp
      (by rw [hsplit, ← heq, add_zero])
    rw [hz] at ha
    exact (not_lt_of_ge ha) hp
  · intro h
    unfold mass
    apply tsum_congr
    intro e
    by_cases hp : p e = 0
    · simp [hp]
    · simp [h e (pos_iff_ne_zero.mpr hp)]

theorem mass_eq_iff_predicates (p : A → ℝ≥0∞) (hfin : (∑' e, p e) ≠ ⊤)
    (hpos : ∀ e, 0 < p e) {B C : A → Prop} (hsub : ∀ e, B e → C e) :
    mass p B = mass p C ↔ B = C := by
  rw [mass_eq_iff_agree_on_support p hfin hsub]
  constructor
  · intro h
    exact funext (fun e => propext (h e (hpos e)))
  · rintro rfl e _
    exact Iff.rfl

theorem gap_eq_sub (p : A → ℝ≥0∞) (hfin : (∑' e, p e) ≠ ⊤)
    (seen : ℕ × A → Bool) (t : ℕ) :
    gap p seen t =
      mass p (fun e => ∃ s, seen (s, e) = true) - mass p (fun e => seen (t, e) = true) := by
  classical
  have hstage : mass p (fun e => seen (t, e) = true) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfin
    have h := mass_mono p (B := fun e => seen (t, e) = true) (C := fun _ => True)
      (fun _ _ => trivial)
    simpa only [mass, if_true] using h
  apply ENNReal.eq_sub_of_add_eq hstage
  unfold gap mass
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro e
  by_cases ht : seen (t, e) = true
  · simp [ht, show ∃ s, seen (s, e) = true from ⟨t, ht⟩]
  · by_cases he : ∃ s, seen (s, e) = true <;> simp [he, ht]

theorem atom_le_gap_of_missing (p : A → ℝ≥0∞) (seen : ℕ × A → Bool)
    {t : ℕ} {e : A} (he : ∃ s, seen (s, e) = true) (ht : seen (t, e) ≠ true) :
    p e ≤ gap p seen t :=
  atom_le_mass p e ⟨he, ht⟩

/-- A dyadic error tolerance. -/
noncomputable def tolerance (k : ℕ) : ℝ≥0∞ := ((2 : ℝ≥0∞)⁻¹) ^ k

/-- The geometric query law, indexed from zero. -/
noncomputable def dyadicWeight (e : ℕ) : ℝ≥0∞ := tolerance (e + 1)

theorem tolerance_pos (k : ℕ) : 0 < tolerance k := by
  unfold tolerance
  exact ENNReal.pow_pos (by simp [ENNReal.inv_pos]) _

theorem tolerance_lt_succ (k : ℕ) : tolerance (k + 1) < tolerance k := by
  have hlt : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  have hne : tolerance k ≠ 0 := (tolerance_pos k).ne'
  have hfin : tolerance k ≠ ⊤ := by
    unfold tolerance
    exact ENNReal.pow_ne_top (a := (2 : ℝ≥0∞)⁻¹) (by simp)
  change ((2 : ℝ≥0∞)⁻¹) ^ (k+1) < tolerance k
  rw [pow_succ]
  change tolerance k * (2 : ℝ≥0∞)⁻¹ < tolerance k
  simpa only [mul_one] using (ENNReal.mul_lt_mul_left' hne hfin hlt)

theorem dyadic_normalized : ∑' e, dyadicWeight e = 1 := by
  unfold dyadicWeight tolerance
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

theorem dyadic_tail (n : ℕ) : ∑' e, (if n ≤ e then dyadicWeight e else 0) = tolerance n := by
  induction n with
  | zero => simpa [tolerance] using dyadic_normalized
  | succ n ih =>
    let f : ℕ → ℝ≥0∞ := fun e => if n + 1 ≤ e then dyadicWeight e else 0
    let g : ℕ → ℝ≥0∞ := fun e => if e = n then dyadicWeight n else 0
    have hg : ∑' e, g e = dyadicWeight n := by
      rw [tsum_eq_single n]
      · simp [g]
      · intro b hb
        simp [g, hb]
    have hterms (e : ℕ) : f e + g e = if n ≤ e then dyadicWeight e else 0 := by
      rcases lt_trichotomy e n with h | rfl | h
      · simp [f, g, Nat.not_le_of_gt h, Nat.ne_of_lt h, show ¬ n+1 ≤ e by omega]
      · simp [f, g]
      · have h₁ : n + 1 ≤ e := by omega
        simp [f, g, h₁, Nat.le_of_lt h, Nat.ne_of_gt h]
    have hsum : (∑' e, f e) + dyadicWeight n = tolerance n := by
      rw [← hg, ← ENNReal.tsum_add]
      simp_rw [hterms]
      exact ih
    have hdouble : tolerance (n + 1) + dyadicWeight n = tolerance n := by
      change tolerance (n + 1) + tolerance (n + 1) = tolerance n
      have hhalf : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := by
        rw [← two_mul]
        exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
      simp only [tolerance, pow_succ, ← mul_add, hhalf, mul_one]
    have hfin : dyadicWeight n ≠ ⊤ :=
      ENNReal.pow_ne_top (a := (2 : ℝ≥0∞)⁻¹) (by simp)
    exact (ENNReal.add_left_inj hfin).mp (hsum.trans hdouble.symm)

/-- A jointly computable Boolean search with a witness for every input. -/
theorem computable_search {test : ℕ × ℕ → Bool} (ht : Computable test)
    (hex : ∀ k, ∃ t, test (k, t) = true) :
    ∃ m : ℕ → ℕ, Computable m ∧ ∀ k, test (k, m k) = true := by
  let search : ℕ → Part ℕ := fun k => Nat.rfind (fun t => Part.some (test (k, t)))
  have hp : Partrec (fun p => Part.some (test p)) := ht
  have hc : Partrec search := Partrec.rfind hp.to₂
  have hd (k : ℕ) : (search k).Dom := by
    obtain ⟨t, h⟩ := hex k
    apply Nat.rfind_dom.2
    exact ⟨t, by simpa using h, fun _ => trivial⟩
  let m k := (search k).get (hd k)
  have hm (k : ℕ) : m k ∈ search k := Part.get_mem (hd k)
  exact ⟨m, Partrec.of_eq_tot hc hm, fun k => by simpa using Nat.rfind_spec (hm k)⟩

/-- A computable tail cutoff turns a finite-prefix stage into a coverage bound. -/
theorem gap_le_tail_of_prefix (p : ℕ → ℝ≥0∞) (seen : ℕ × ℕ → Bool)
    {t n : ℕ}
    (h : ∀ e < n, (∃ s, seen (s, e) = true) → seen (t, e) = true) :
    gap p seen t ≤ ∑' e, (if n ≤ e then p e else 0) := by
  classical
  apply ENNReal.tsum_le_tsum
  intro e
  by_cases hn : n ≤ e
  · rw [if_pos hn]
    split
    · exact le_rfl
    · exact zero_le _
  · have ha : ¬ ((∃ s, seen (s, e) = true) ∧ seen (t, e) ≠ true) :=
      fun hlate => hlate.2 (h e (Nat.lt_of_not_ge hn) hlate.1)
    rw [if_neg hn, if_neg ha]

/-- At each finite prefix a monotone exhaustion reaches its eventual labels. -/
theorem exists_exact_prefix (seen : ℕ × ℕ → Bool)
    (hmono : ∀ {t s : ℕ}, t ≤ s → ∀ e, seen (t, e) = true → seen (s, e) = true) (n : ℕ) :
    ∃ t, ∀ e < n, (∃ s, seen (s, e) = true) → seen (t, e) = true := by
  classical
  induction n with
  | zero => exact ⟨0, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      by_cases hnew : ∃ s, seen (s, n) = true
      · obtain ⟨s, hs⟩ := hnew
        refine ⟨max t s, fun e he heventual => ?_⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with hlt | rfl
        · exact hmono (le_max_left _ _) _ (ht _ hlt heventual)
        · exact hmono (le_max_right _ _) _ hs
      · refine ⟨t, fun e he heventual => ?_⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with hlt | rfl
        · exact ht _ hlt heventual
        · exact (hnew heventual).elim

/-- A finite prefix equality test, computed by bounded recursion. -/
def agreesOnPrefix (seen : ℕ × ℕ → Bool) (label : ℕ → Bool) (t : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => agreesOnPrefix seen label t n && (seen (t, n) == label n)

theorem agreesOnPrefix_eq_true (seen : ℕ × ℕ → Bool) (label : ℕ → Bool) (t n : ℕ) :
    agreesOnPrefix seen label t n = true ↔ ∀ e < n, seen (t, e) = label e := by
  induction n with
  | zero => simp [agreesOnPrefix]
  | succ n ih =>
      rw [agreesOnPrefix, Bool.and_eq_true, ih, beq_iff_eq]
      constructor
      · rintro ⟨hp, hn⟩ e he
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with h | rfl
        · exact hp _ h
        · exact hn
      · intro h
        exact ⟨fun e he => h _ (Nat.lt_succ_of_lt he), h _ (Nat.lt_succ_self _)⟩

set_option maxHeartbeats 2000000 in
theorem agreesOnPrefix_computable {seen : ℕ × ℕ → Bool} {label : ℕ → Bool}
    (hs : Computable seen) (hl : Computable label) :
    Computable fun a : ℕ × ℕ => agreesOnPrefix seen label a.1 a.2 := by
  let step := fun (a : ℕ × ℕ) (b : ℕ × Bool) => b.2 && (seen (a.1, b.1) == label b.1)
  have hf : Computable₂ step := by
    let prev : (ℕ × ℕ) × (ℕ × Bool) → Bool := fun p => p.2.2
    let j : (ℕ × ℕ) × (ℕ × Bool) → ℕ := fun p => p.2.1
    have hj : Computable j := Computable.fst.comp Computable.snd
    have hprev : Computable prev := Computable.snd.comp Computable.snd
    have hv := hs.comp ((Computable.fst.comp Computable.fst).pair hj)
    have hbeq : Computable₂ ((· == ·) : Bool → Bool → Bool) := by
      exact (Primrec.beq.to_comp : Computable (fun p : Bool × Bool => p.1 == p.2))
    have hand : Computable₂ ((· && ·) : Bool → Bool → Bool) :=
      (Primrec.and.to_comp : Computable (fun p : Bool × Bool => p.1 && p.2))
    exact hand.comp hprev (hbeq.comp hv (hl.comp hj))
  refine (Computable.nat_rec Computable.snd (Computable.const true) hf).of_eq ?_
  intro a
  cases a with
  | mk t n =>
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa [step, agreesOnPrefix] using
        congrArg (fun prior => prior && (seen (t, n) == label n)) ih

/-- Any effective positive lower atom scales suffice to recover the eventual domain. -/
theorem computable_domain_of_modulus {A : Type*} [Primcodable A]
    (p : A → ℝ≥0∞) (seen : ℕ × A → Bool) (hs : Computable seen)
    (precision : A → ℕ) (hp : Computable precision)
    (hlow : ∀ e, tolerance (precision e) ≤ p e)
    {m : ℕ → ℕ} (hm : Computable m) (hmod : ∀ k, gap p seen (m k) < tolerance k) :
    ComputablePred (fun e => ∃ t, seen (t, e) = true) := by
  refine ComputablePred.computable_iff.mpr ⟨fun e => seen (m (precision e), e),
    hs.comp ((hm.comp hp).pair Computable.id), ?_⟩
  funext e
  apply propext
  constructor
  · intro he
    by_contra ht
    exact (not_lt_of_ge <| (hlow e).trans (atom_le_gap_of_missing p seen he ht)) (hmod _)
  · intro ht
    exact ⟨m (precision e), ht⟩

/-- A computable eventual domain and computable tail cutoffs give an effective modulus. -/
theorem computable_modulus_of_domain (p : ℕ → ℝ≥0∞) (seen : ℕ × ℕ → Bool)
    (hs : Computable seen)
    (hmono : ∀ {t s : ℕ}, t ≤ s → ∀ e, seen (t, e) = true → seen (s, e) = true)
    (hA : ComputablePred (fun e => ∃ t, seen (t, e) = true))
    (cutoff : ℕ → ℕ) (hc : Computable cutoff)
    (hcut : ∀ k, (∑' e, (if cutoff k ≤ e then p e else 0)) < tolerance k) :
    ∃ m : ℕ → ℕ, Computable m ∧ ∀ k, gap p seen (m k) < tolerance k := by
  obtain ⟨label, hlabel, heq⟩ := ComputablePred.computable_iff.mp hA
  let test (a : ℕ × ℕ) := agreesOnPrefix seen label a.2 (cutoff a.1)
  have htest : Computable test :=
    (agreesOnPrefix_computable hs hlabel).comp (Computable.snd.pair (hc.comp Computable.fst))
  have hlabel' (e : ℕ) : (∃ s, seen (s, e) = true) ↔ label e = true :=
    Iff.of_eq (congrFun heq e)
  have hfound (k : ℕ) : ∃ t, test (k, t) = true := by
    obtain ⟨t, ht⟩ := exists_exact_prefix seen hmono (cutoff k)
    refine ⟨t, (agreesOnPrefix_eq_true _ _ _ _).mpr (fun e he => ?_)⟩
    have ht' : seen (t, e) = true ↔ label e = true :=
      ⟨fun ht => (hlabel' e).mp ⟨t, ht⟩, fun hl => ht e he ((hlabel' e).mpr hl)⟩
    cases hs : seen (t, e) <;> cases hl : label e <;> simp_all
  obtain ⟨m, hm, hm'⟩ := computable_search htest hfound
  refine ⟨m, hm, fun k => lt_of_le_of_lt ?_ (hcut k)⟩
  apply gap_le_tail_of_prefix
  intro e he h
  rw [(agreesOnPrefix_eq_true _ _ _ _).mp (hm' k) e he]
  exact (hlabel' e).mp h

/-- The domain/modulus equivalence for actual dyadic probabilities on all of ℕ. -/
theorem dyadic_domain_iff_modulus (seen : ℕ × ℕ → Bool) (hs : Computable seen)
    (hmono : ∀ {t s : ℕ}, t ≤ s → ∀ e, seen (t, e) = true → seen (s, e) = true) :
    ComputablePred (fun e => ∃ t, seen (t, e) = true) ↔
      ∃ m : ℕ → ℕ, Computable m ∧ ∀ k,
        mass dyadicWeight (fun e => ∃ s, seen (s, e) = true) -
          mass dyadicWeight (fun e => seen (m k, e) = true) < tolerance k := by
  have hfinite : (∑' e, dyadicWeight e) ≠ ⊤ := by rw [dyadic_normalized]; simp
  simp_rw [← gap_eq_sub dyadicWeight hfinite]
  constructor
  · intro hA
    exact computable_modulus_of_domain dyadicWeight seen hs hmono hA Nat.succ
      Computable.succ (fun k => by rw [dyadic_tail]; exact tolerance_lt_succ k)
  · rintro ⟨m, hm, hmod⟩
    exact computable_domain_of_modulus dyadicWeight seen hs Nat.succ Computable.succ
      (fun _ => le_rfl) hm hmod

/-- A dyadic prefix interpreted as a natural numerator. -/
def prefixNumerator (label : ℕ × ℕ → Bool) (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * prefixNumerator label t n + (if label (t,n) then 1 else 0)

set_option maxHeartbeats 2000000 in
theorem prefixNumerator_computable {label : ℕ × ℕ → Bool} (hl : Computable label) :
    Computable fun a : ℕ × ℕ => prefixNumerator label a.1 a.2 := by
  let step (a : ℕ × ℕ) (b : ℕ × ℕ) :=
    2 * b.2 + (if label (a.1,b.1) then 1 else 0)
  have hstep : Computable₂ step := by
    let domain := (ℕ × ℕ) × (ℕ × ℕ)
    have ht : Computable (fun p : domain => p.1.1) := Computable.fst.comp Computable.fst
    have hn : Computable (fun p : domain => p.2.1) := Computable.fst.comp Computable.snd
    have hp : Computable (fun p : domain => p.2.2) := Computable.snd.comp Computable.snd
    have hadd : Computable₂ ((· + ·) : ℕ → ℕ → ℕ) := Primrec.nat_add.to_comp
    have hmul : Computable₂ ((· * ·) : ℕ → ℕ → ℕ) := Primrec.nat_mul.to_comp
    have hb : Computable (fun p : domain => if label (p.1.1,p.2.1) then (1 : ℕ) else 0) :=
      (Computable.cond (hl.comp (ht.pair hn)) (Computable.const 1) (Computable.const 0)).of_eq
        (fun p => by cases label (p.1.1,p.2.1) <;> rfl)
    exact hadd.comp (hmul.comp (Computable.const 2) hp) hb
  refine (Computable.nat_rec Computable.snd (Computable.const 0) hstep).of_eq ?_
  intro a
  cases a with
  | mk t n =>
    induction n with
    | zero => rfl
    | succ n ih =>
      simp [step, prefixNumerator, ih]

theorem tolerance_succ_scale (n : ℕ) : 2 * tolerance (n+1) = tolerance n := by
  unfold tolerance
  rw [pow_succ, mul_comm _ (((2 : ℝ≥0∞)⁻¹)^n * _), mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by simp), mul_one]

theorem prefixNumerator_value (label : ℕ × ℕ → Bool) (t n : ℕ) :
    (prefixNumerator label t n : ℝ≥0∞) * tolerance n =
      ∑ e ∈ Finset.range n, if label (t,e) then dyadicWeight e else 0 := by
  induction n with
  | zero => simp [prefixNumerator]
  | succ n ih =>
    rw [prefixNumerator, Finset.sum_range_succ, ← ih, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, add_mul, mul_comm (2 : ℝ≥0∞) _, mul_assoc, tolerance_succ_scale]
    congr 1
    cases label (t,n) <;> simp [dyadicWeight]

theorem prefix_mass_bounds (label : ℕ × ℕ → Bool) (t n : ℕ) :
    let q := (prefixNumerator label t n : ℝ≥0∞) * tolerance n
    q ≤ mass dyadicWeight (fun e => label (t,e) = true) ∧
      mass dyadicWeight (fun e => label (t,e) = true) ≤ q + tolerance n := by
  classical
  dsimp only
  rw [prefixNumerator_value]
  constructor
  · unfold mass
    apply le_trans _ (ENNReal.sum_le_tsum (Finset.range n))
    apply Finset.sum_le_sum
    intro e _
    by_cases he : label (t,e) = true <;> simp [he]
  · unfold mass
    have hprefix : (∑' e, if e < n ∧ label (t,e) = true then dyadicWeight e else 0) =
        ∑ e ∈ Finset.range n, if label (t,e) then dyadicWeight e else 0 := by
      rw [tsum_eq_sum (s := Finset.range n)]
      · apply Finset.sum_congr rfl
        intro e he
        simp [Finset.mem_range.mp he]
      · intro e he
        have h : ¬ e < n := fun h => he (Finset.mem_range.mpr h)
        simp [h]
    rw [← dyadic_tail n, ← hprefix, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro e
    by_cases he : e < n
    · by_cases hl : label (t,e) = true <;> simp [he, Nat.not_le_of_gt he, hl]
    · by_cases hl : label (t,e) = true <;> simp [he, Nat.le_of_not_gt he, hl]

/-- A computable dyadic Cauchy name, with denominators fixed to powers of two. -/
def DyadicComputable (x : ℝ≥0∞) : Prop :=
  ∃ code : ℕ → ℕ, Computable code ∧ ∀ n,
    let q := (code n : ℝ≥0∞) * tolerance n
    q ≤ x + tolerance n ∧ x ≤ q + tolerance n

theorem dyadic_computable_mass_of_domain (seen : ℕ × ℕ → Bool)
    (hA : ComputablePred (fun e => ∃ t, seen (t,e) = true)) :
    DyadicComputable (mass dyadicWeight (fun e => ∃ t, seen (t,e) = true)) := by
  obtain ⟨label, hlabel, heq⟩ := ComputablePred.computable_iff.mp hA
  let label' (a : ℕ × ℕ) := label a.2
  have h : Computable label' := hlabel.comp Computable.snd
  refine ⟨prefixNumerator label' 0, (prefixNumerator_computable h).comp
    ((Computable.const 0).pair Computable.id), fun n => ?_⟩
  have hb := prefix_mass_bounds label' 0 n
  rw [heq]
  exact ⟨hb.1.trans (le_add_right le_rfl), hb.2⟩

theorem dyadic_mass_lt_add_tol (seen : ℕ × ℕ → Bool)
    (hmono : ∀ {t s : ℕ}, t ≤ s → ∀ e, seen (t, e) = true → seen (s, e) = true) (n : ℕ) :
    ∃ t, mass dyadicWeight (fun e => ∃ s, seen (s,e) = true) <
      mass dyadicWeight (fun e => seen (t,e) = true) + tolerance n := by
  obtain ⟨t, ht⟩ := exists_exact_prefix seen hmono (n+1)
  have hfin : (∑' e, dyadicWeight e) ≠ ⊤ := by rw [dyadic_normalized]; simp
  have hgap := gap_le_tail_of_prefix dyadicWeight seen ht
  rw [dyadic_tail, gap_eq_sub dyadicWeight hfin] at hgap
  have hle := mass_mono dyadicWeight (B := fun e => seen (t,e) = true)
    (C := fun e => ∃ s, seen (s,e) = true) (fun e he => ⟨t, he⟩)
  have hstage : mass dyadicWeight (fun e => seen (t,e) = true) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfin
    have h := mass_mono dyadicWeight (B := fun e => seen (t,e) = true) (C := fun _ => True)
      (fun _ _ => trivial)
    simpa only [mass, if_true] using h
  refine ⟨t, ?_⟩
  rw [add_comm, ← ENNReal.sub_lt_iff_lt_right hstage hle]
  exact hgap.trans_lt (tolerance_lt_succ n)

theorem tolerance_shift_three (k : ℕ) : 8 * tolerance (k+3) = tolerance k := by
  calc
    8 * tolerance (k+3) = 2 * (2 * (2 * tolerance (k+3))) := by ring
    _ = tolerance k := by rw [tolerance_succ_scale, tolerance_succ_scale, tolerance_succ_scale]

theorem scaled_nat_lt_iff (a b n : ℕ) :
    (a : ℝ≥0∞) * tolerance n < (b : ℝ≥0∞) * tolerance n ↔ a < b := by
  have hne : tolerance n ≠ 0 := (tolerance_pos n).ne'
  have hfin : tolerance n ≠ ⊤ :=
    ENNReal.pow_ne_top (a := (2 : ℝ≥0∞)⁻¹) (by simp)
  rw [ENNReal.mul_lt_mul_right hne hfin]
  norm_cast

theorem scaled_nat_add (a b n : ℕ) :
    ((a+b : ℕ) : ℝ≥0∞) * tolerance n =
      (a : ℝ≥0∞) * tolerance n + (b : ℝ≥0∞) * tolerance n := by
  rw [Nat.cast_add, add_mul]

set_option maxHeartbeats 2000000 in
theorem dyadic_modulus_of_computable_mass (seen : ℕ × ℕ → Bool) (hs : Computable seen)
    (hmono : ∀ {t s : ℕ}, t ≤ s → ∀ e, seen (t, e) = true → seen (s, e) = true)
    (hx : DyadicComputable (mass dyadicWeight (fun e => ∃ t, seen (t,e) = true))) :
    ∃ m : ℕ → ℕ, Computable m ∧ ∀ k,
      mass dyadicWeight (fun e => ∃ t, seen (t,e) = true) -
        mass dyadicWeight (fun e => seen (m k,e) = true) < tolerance k := by
  obtain ⟨code, hcode, happ⟩ := hx
  let test (a : ℕ × ℕ) := decide (code (a.1+3) + 1 < prefixNumerator seen a.2 (a.1+3) + 8)
  have htest : Computable test := by
    have hn : Computable (fun a : ℕ × ℕ => a.1+3) :=
      Primrec.nat_add.to_comp.comp Computable.fst (Computable.const 3)
    have hleft : Computable (fun a : ℕ × ℕ => code (a.1+3)+1) :=
      (Primrec.nat_add.to_comp : Computable₂ ((·+·) : ℕ → ℕ → ℕ)).comp
        (hcode.comp hn) (Computable.const 1)
    have hright : Computable (fun a : ℕ × ℕ => prefixNumerator seen a.2 (a.1+3)+8) :=
      (Primrec.nat_add.to_comp : Computable₂ ((·+·) : ℕ → ℕ → ℕ)).comp
        ((prefixNumerator_computable hs).comp (Computable.snd.pair hn)) (Computable.const 8)
    exact (Primrec.nat_lt.to_comp : Computable₂ fun a b : ℕ => decide (a<b)).comp hleft hright
  have test_iff (k t : ℕ) :
      test (k,t) = true ↔
        (code (k+3) : ℝ≥0∞) * tolerance (k+3) + tolerance (k+3) <
          (prefixNumerator seen t (k+3) : ℝ≥0∞) * tolerance (k+3) + tolerance k := by
    dsimp [test]
    rw [decide_eq_true_eq, ← scaled_nat_lt_iff _ _ (k+3), scaled_nat_add, scaled_nat_add]
    simp [tolerance_shift_three]
  have hfound (k : ℕ) : ∃ t, test (k,t) = true := by
    obtain ⟨t, ht⟩ := dyadic_mass_lt_add_tol seen hmono (k+3)
    refine ⟨t, (test_iff k t).mpr ?_⟩
    let x := mass dyadicWeight (fun e => ∃ t, seen (t,e) = true)
    let q := (code (k+3) : ℝ≥0∞) * tolerance (k+3)
    let r := (prefixNumerator seen t (k+3) : ℝ≥0∞) * tolerance (k+3)
    let ε := tolerance (k+3)
    have hq : q ≤ x + ε := (happ (k+3)).1
    have hxr : x ≤ r + ε + ε := ht.le.trans
      (add_le_add_right (prefix_mass_bounds seen t (k+3)).2 ε)
    have hε : 0 < ε := tolerance_pos _
    have hsmall : 4 * ε < tolerance k := by
      rw [← tolerance_shift_three k]
      exact (ENNReal.mul_lt_mul_right hε.ne'
        (ENNReal.pow_ne_top (a := (2 : ℝ≥0∞)⁻¹) (by simp))).mpr (by norm_num)
    change q + ε < r + tolerance k
    calc
      q + ε ≤ x + ε + ε := add_le_add_right hq ε
      _ ≤ r + ε + ε + ε + ε := add_le_add_right (add_le_add_right hxr ε) ε
      _ = r + 4 * ε := by ring
      _ < r + tolerance k := by
        apply ENNReal.add_lt_add_left _ hsmall
        apply ne_top_of_le_ne_top (b := 1)
        · simp
        · exact (prefix_mass_bounds seen t (k+3)).1.trans
            (dyadic_normalized ▸ (by
              have h := mass_mono dyadicWeight
                (B := fun e => seen (t,e) = true) (C := fun _ => True) (fun _ _ => trivial)
              simpa only [mass, if_true] using h))
  obtain ⟨m, hm, hmatch⟩ := computable_search htest hfound
  refine ⟨m, hm, fun k => ?_⟩
  have htest' := (test_iff k (m k)).mp (hmatch k)
  have hq := (happ (k+3)).2
  have hprefix := (prefix_mass_bounds seen (m k) (k+3)).1
  have hfin : mass dyadicWeight (fun e => seen (m k,e) = true) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ∑' e, dyadicWeight e)
    · rw [dyadic_normalized]
      simp
    · have h := mass_mono dyadicWeight (B := fun e => seen (m k,e) = true)
        (C := fun _ => True) (fun _ _ => trivial)
      simpa only [mass, if_true] using h
  rw [ENNReal.sub_lt_iff_lt_right hfin
    (mass_mono dyadicWeight (fun e he => ⟨m k, he⟩)), add_comm]
  exact hq.trans_lt (htest'.trans_le (add_le_add_right hprefix _))

theorem dyadic_domain_iff_computable_mass (seen : ℕ × ℕ → Bool) (hs : Computable seen)
    (hmono : ∀ {t s : ℕ}, t ≤ s → ∀ e, seen (t, e) = true → seen (s, e) = true) :
    ComputablePred (fun e => ∃ t, seen (t,e) = true) ↔
      DyadicComputable (mass dyadicWeight (fun e => ∃ t, seen (t,e) = true)) :=
  ⟨dyadic_computable_mass_of_domain seen, fun hx =>
    (dyadic_domain_iff_modulus seen hs hmono).mpr (dyadic_modulus_of_computable_mass seen hs hmono hx)⟩

#print axioms mass_eq_iff_agree_on_support
#print axioms mass_eq_iff_predicates
#print axioms gap_eq_sub
#print axioms atom_le_gap_of_missing
#print axioms dyadic_normalized
#print axioms dyadic_tail
#print axioms computable_domain_of_modulus
#print axioms computable_modulus_of_domain
#print axioms dyadic_domain_iff_modulus
#print axioms dyadic_domain_iff_computable_mass
#print axioms dyadic_modulus_of_computable_mass

end EpistemicSelfKnowledge.CoverageMeasure
