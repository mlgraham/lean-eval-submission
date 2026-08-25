import ChallengeDeps
import Mathlib.Tactic.SplitIfs

/-!
# de Bruijn algebra for `lift` and `subst`

The standard commutation lemmas (cf. Barras's Coq development of CC): merging and permuting
lifts, distributing a lift over a substitution, cancelling a substitution against a fresh
lift, and distributing substitutions over each other. All proofs are by induction on the term
with `omega` for the index arithmetic.
-/

namespace Submission.Syntax

open LeanEval.ProgramVerification.CoCStrongNormalization

/-! ### Lifting -/

@[simp] theorem lift_zero (c : Nat) (t : Tm) : lift 0 c t = t := by
  induction t generalizing c with
  | var i =>
    simp only [lift]
    split_ifs <;> first | rfl | (congr 1; omega)
  | srt s => rfl
  | app f a ihf iha => simp [lift, ihf, iha]
  | lam A b ihA ihb => simp [lift, ihA, ihb]
  | pi A B ihA ihB => simp [lift, ihA, ihB]

/-- Merging two lifts: `c ≤ c' ≤ c + d → lift d' c' (lift d c t) = lift (d + d') c t`. -/
theorem lift_lift_merge (d d' c c' : Nat) (t : Tm) (h₁ : c ≤ c') (h₂ : c' ≤ c + d) :
    lift d' c' (lift d c t) = lift (d + d') c t := by
  induction t generalizing c c' with
  | var i =>
    simp only [lift, subst]
    split_ifs <;> (try simp only [lift, subst]) <;> (try split_ifs) <;>
      first | rfl | (exfalso; omega) | (congr 1; omega)
  | srt s => rfl
  | app f a ihf iha => simp [lift, ihf c c' h₁ h₂, iha c c' h₁ h₂]
  | lam A b ihA ihb =>
    simp [lift, ihA c c' h₁ h₂, ihb (c + 1) (c' + 1) (by omega) (by omega)]
  | pi A B ihA ihB =>
    simp [lift, ihA c c' h₁ h₂, ihB (c + 1) (c' + 1) (by omega) (by omega)]

/-- Permuting two lifts: `c ≤ c' → lift d c (lift d' c' t) = lift d' (c' + d) (lift d c t)`. -/
theorem lift_lift_permute (d d' c c' : Nat) (t : Tm) (h : c ≤ c') :
    lift d c (lift d' c' t) = lift d' (c' + d) (lift d c t) := by
  induction t generalizing c c' with
  | var i =>
    simp only [lift, subst]
    split_ifs <;> (try simp only [lift, subst]) <;> (try split_ifs) <;>
      first | rfl | (exfalso; omega) | (congr 1; omega)
  | srt s => rfl
  | app f a ihf iha => simp [lift, ihf c c' h, iha c c' h]
  | lam A b ihA ihb =>
    simp only [lift, ihA c c' h, ihb (c + 1) (c' + 1) (by omega)]
    rw [show c' + 1 + d = c' + d + 1 by omega]
  | pi A B ihA ihB =>
    simp only [lift, ihA c c' h, ihB (c + 1) (c' + 1) (by omega)]
    rw [show c' + 1 + d = c' + d + 1 by omega]

/-! ### Substitution against lifting -/

/-- A substitution at a freshly lifted position cancels:
`c ≤ k < c + d → subst k u (lift d c t) = lift (d - 1) c t`. -/
theorem subst_lift_cancel (d c k : Nat) (u t : Tm) (h₁ : c ≤ k) (h₂ : k < c + d) :
    subst k u (lift d c t) = lift (d - 1) c t := by
  induction t generalizing c k with
  | var i =>
    simp only [lift, subst]
    split_ifs <;> (try simp only [lift, subst]) <;> (try split_ifs) <;>
      first | rfl | (exfalso; omega) | (congr 1; omega)
  | srt s => rfl
  | app f a ihf iha => simp [lift, subst, ihf c k h₁ h₂, iha c k h₁ h₂]
  | lam A b ihA ihb =>
    simp [lift, subst, ihA c k h₁ h₂, ihb (c + 1) (k + 1) (by omega) (by omega)]
  | pi A B ihA ihB =>
    simp [lift, subst, ihA c k h₁ h₂, ihB (c + 1) (k + 1) (by omega) (by omega)]

/-- Lifting distributes over a substitution below the lift:
`k ≤ c → lift d c (subst k u t) = subst k (lift d (c - k) u) (lift d (c + 1) t)`. -/
theorem lift_subst_distr (d c k : Nat) (u t : Tm) (h : k ≤ c) :
    lift d c (subst k u t) = subst k (lift d (c - k) u) (lift d (c + 1) t) := by
  induction t generalizing c k with
  | var i =>
    by_cases h2 : i = k
    · subst h2
      simp only [lift, subst]
      split_ifs <;> (try simp only [lift, subst]) <;> (try split_ifs) <;>
        first | rfl | (exfalso; omega) | (congr 1; omega) | skip
      all_goals
        -- `lift d c (lift i 0 u) = lift i 0 (lift d (c - i) u)`
        have := lift_lift_permute i d 0 (c - i) u (Nat.zero_le _)
        rw [show c - i + i = c by omega] at this
        exact this.symm
    · simp only [lift, subst]
      split_ifs <;> (try simp only [lift, subst]) <;> (try split_ifs) <;>
        first | rfl | (exfalso; omega) | (congr 1; omega)
  | srt s => rfl
  | app f a ihf iha => simp [lift, subst, ihf c k h, iha c k h]
  | lam A b ihA ihb =>
    simp only [lift, subst, ihA c k h, ihb (c + 1) (k + 1) (by omega)]
    rw [show c + 1 - (k + 1) = c - k by omega]
  | pi A B ihA ihB =>
    simp only [lift, subst, ihA c k h, ihB (c + 1) (k + 1) (by omega)]
    rw [show c + 1 - (k + 1) = c - k by omega]

/-- Lifting distributes over a substitution above the lift:
`c ≤ k → lift d c (subst k u t) = subst (k + d) u (lift d c t)`. -/
theorem lift_subst_distr' (d c k : Nat) (u t : Tm) (h : c ≤ k) :
    lift d c (subst k u t) = subst (k + d) u (lift d c t) := by
  induction t generalizing c k with
  | var i =>
    by_cases h2 : i = k
    · subst h2
      simp only [lift, subst]
      split_ifs <;> (try simp only [lift, subst]) <;> (try split_ifs) <;>
        first | rfl | (exfalso; omega) | (congr 1; omega) | skip
      all_goals exact lift_lift_merge i d 0 c u (Nat.zero_le _) (by omega)
    · simp only [lift, subst]
      split_ifs <;> (try simp only [lift, subst]) <;> (try split_ifs) <;>
        first | rfl | (exfalso; omega) | (congr 1; omega)
  | srt s => rfl
  | app f a ihf iha => simp [lift, subst, ihf c k h, iha c k h]
  | lam A b ihA ihb =>
    simp only [lift, subst, ihA c k h, ihb (c + 1) (k + 1) (by omega)]
    rw [show k + 1 + d = k + d + 1 by omega]
  | pi A B ihA ihB =>
    simp only [lift, subst, ihA c k h, ihB (c + 1) (k + 1) (by omega)]
    rw [show k + 1 + d = k + d + 1 by omega]

/-- A substitution above a lift commutes past it:
`c + d ≤ k → subst k u (lift d c t) = lift d c (subst (k - d) u t)`. -/
theorem subst_lift_comm (d c k : Nat) (u t : Tm) (h : c + d ≤ k) :
    subst k u (lift d c t) = lift d c (subst (k - d) u t) := by
  have := lift_subst_distr' d c (k - d) u t (by omega)
  rw [show k - d + d = k by omega] at this
  exact this.symm

/-! ### Substitution against substitution -/

/-- Distributing substitutions:
`j ≤ k → subst k u (subst j v t) = subst j (subst (k - j) u v) (subst (k + 1) u t)`. -/
theorem subst_subst_distr (j k : Nat) (u v t : Tm) (h : j ≤ k) :
    subst k u (subst j v t) = subst j (subst (k - j) u v) (subst (k + 1) u t) := by
  induction t generalizing j k with
  | var i =>
    by_cases h2 : i = j
    · subst h2
      simp only [subst]
      split_ifs <;> (try simp only [subst]) <;> (try split_ifs) <;>
        first | rfl | (exfalso; omega) | (congr 1; omega) | skip
      all_goals exact subst_lift_comm i 0 k u v (by omega)
    · by_cases h4 : i = k + 1
      · subst h4
        simp only [subst]
        split_ifs <;> (try simp only [subst]) <;> (try split_ifs) <;>
          first | rfl | (exfalso; omega) | (congr 1; omega) | skip
        all_goals
          rw [subst_lift_cancel (k + 1) 0 j _ u (Nat.zero_le _) (by omega)]
          simp
      · simp only [subst]
        split_ifs <;> (try simp only [subst]) <;> (try split_ifs) <;>
          first | rfl | (exfalso; omega) | (congr 1; omega)
  | srt s => rfl
  | app f a ihf iha => simp [subst, ihf j k h, iha j k h]
  | lam A b ihA ihb =>
    simp only [subst, ihA j k h, ihb (j + 1) (k + 1) (by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | pi A B ihA ihB =>
    simp only [subst, ihA j k h, ihB (j + 1) (k + 1) (by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]

end Submission.Syntax
