import Mathlib.Computability.Halting

namespace EpistemicCeiling

def Homogeneous (obs : ℕ → ℕ) (atom : ℕ → Bool) (i : ℕ) : Prop :=
  ∀ s t, obs s = i → obs t = i → atom s = atom t

def Sound (obs : ℕ → ℕ) (atom : ℕ → Bool) (accept : ℕ → Bool → ℕ → Bool) : Prop :=
  ∀ s b w, accept (obs s) b w = true → atom s = b

theorem ambiguity_iff (obs : ℕ → ℕ) (atom : ℕ → Bool) (i : ℕ) :
    ¬ Homogeneous obs atom i ↔
      ∃ s t, obs s = i ∧ obs t = i ∧ atom s ≠ atom t := by
  classical
  simp [Homogeneous, not_forall, Classical.not_imp]

theorem domain_subset_homogeneous (obs : ℕ → ℕ) (atom : ℕ → Bool)
    {accept : ℕ → Bool → ℕ → Bool} (sound : Sound obs atom accept) {i : ℕ}
    (h : ∃ b w, accept i b w = true) : Homogeneous obs atom i := by
  obtain ⟨b, w, hw⟩ := h
  intro s t hs ht
  exact (sound s b w (by simpa [hs] using hw)).trans
    (sound t b w (by simpa [ht] using hw)).symm

open Computable

theorem re_exists_test {f : ℕ × ℕ → Bool} (hf : Computable f) :
    REPred fun i => ∃ n, f (i,n) = true := by
  have hp : Partrec (fun p : ℕ × ℕ => Part.some (f p)) := hf
  have hs : Partrec fun i => Nat.rfind (fun n => Part.some (f (i,n))) :=
    Partrec.rfind hp.to₂
  exact hs.dom_re.of_eq (fun i => by simp [Nat.rfind_dom])

def AmbiguityWitness (obs : ℕ → ℕ) (atom : ℕ → Bool) (input : ℕ × ℕ) : Bool :=
  (obs input.2.unpair.1 == input.1) &&
    (obs input.2.unpair.2 == input.1) && !(atom input.2.unpair.1 == atom input.2.unpair.2)

theorem ambiguity_test_computable (obs : ℕ → ℕ) (atom : ℕ → Bool)
    (ho : Computable obs) (ha : Computable atom) : Computable (AmbiguityWitness obs atom) := by
  have hp : Computable (fun p : ℕ × ℕ => p.2.unpair) := unpair.comp snd
  have h₁ := fst.comp hp
  have h₂ := snd.comp hp
  have hb₁ := (Primrec.beq (α := ℕ)).to_comp.comp (ho.comp h₁) fst
  have hb₂ := (Primrec.beq (α := ℕ)).to_comp.comp (ho.comp h₂) fst
  have hb₃ := Primrec.not.to_comp.comp ((Primrec.beq (α := Bool)).to_comp.comp (ha.comp h₁) (ha.comp h₂))
  exact Primrec.and.to_comp.comp (Primrec.and.to_comp.comp hb₁ hb₂) hb₃

theorem ambiguity_test_iff (obs : ℕ → ℕ) (atom : ℕ → Bool) (i : ℕ) :
    (∃ w, AmbiguityWitness obs atom (i,w) = true) ↔ ¬ Homogeneous obs atom i := by
  rw [ambiguity_iff]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.unpair.1, w.unpair.2, by simpa [AmbiguityWitness, and_assoc] using hw⟩
  · rintro ⟨s, t, hs, ht, hne⟩
    refine ⟨Nat.pair s t, ?_⟩
    simp [AmbiguityWitness, hs, ht, hne]

theorem ambiguity_re (obs : ℕ → ℕ) (atom : ℕ → Bool)
    (ho : Computable obs) (ha : Computable atom) :
    REPred fun i => ¬ Homogeneous obs atom i :=
  (re_exists_test (ambiguity_test_computable obs atom ho ha)).of_eq
    (ambiguity_test_iff obs atom)

theorem decidable_of_complete_certificate_test
    (obs : ℕ → ℕ) (atom : ℕ → Bool)
    (ho : Computable obs) (ha : Computable atom)
    (test : ℕ × ℕ → Bool) (ht : Computable test)
    (complete : ∀ i, (∃ w, test (i,w) = true) ↔ Homogeneous obs atom i) :
    ComputablePred (Homogeneous obs atom) :=
  ComputablePred.computable_iff_re_compl_re'.2
    ⟨(re_exists_test ht).of_eq complete, ambiguity_re obs atom ho ha⟩

#print axioms ambiguity_iff
#print axioms domain_subset_homogeneous
#print axioms re_exists_test
#print axioms ambiguity_test_computable
#print axioms ambiguity_test_iff
#print axioms ambiguity_re
#print axioms decidable_of_complete_certificate_test

end EpistemicCeiling
