import ChallengeDeps
import Mathlib.Tactic.SplitIfs
import Submission.Syntax
import Submission.Confluence

/-!
# Weakening

`Ins n Γ Γ'` says `Γ'` is `Γ` with one well-typed binding inserted at depth `n` (the `n` most
recent bindings are lifted accordingly). Weakening: `Typing Γ t A → Ins n Γ Γ' →
Typing Γ' (lift 1 n t) (lift 1 n A)`, mutually with `Wf Γ → Ins n Γ Γ' → Wf Γ'`.
-/

namespace LeanEval.ProgramVerification.CoCStrongNormalization

open Submission.Syntax

/-- Insertion of a well-typed binding at depth `n`. -/
inductive Ins : Nat → List Tm → List Tm → Prop where
  | zero {Γ : List Tm} {B : Tm} {s : Srt} : Typing Γ B (.srt s) → Ins 0 Γ (B :: Γ)
  | succ {n : Nat} {Γ Γ' : List Tm} {A : Tm} : Ins n Γ Γ' → Ins (n + 1) (A :: Γ) (lift 1 n A :: Γ')

/-- Looking up below the insertion point. -/
theorem Ins.get_lt {n : Nat} {Γ Γ' : List Tm} (h : Ins n Γ Γ') {i : Nat} {A : Tm}
    (hi : i < n) (hget : Γ[i]? = some A) : Γ'[i]? = some (lift 1 (n - 1 - i) A) := by
  induction h generalizing i with
  | zero _ => omega
  | succ _ ih =>
    rename_i n Γ Γ' A'
    cases i with
    | zero => simp at hget ⊢; subst hget; simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget ⊢
      rw [ih (by omega) hget]
      congr 2; omega

/-- Looking up at or above the insertion point. -/
theorem Ins.get_ge {n : Nat} {Γ Γ' : List Tm} (h : Ins n Γ Γ') {i : Nat} {A : Tm}
    (hi : n ≤ i) (hget : Γ[i]? = some A) : Γ'[i + 1]? = some A := by
  induction h generalizing i with
  | zero _ => simpa using hget
  | succ _ ih =>
    cases i with
    | zero => omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget ⊢
      exact ih (by omega) hget

/-- Motive for contexts. -/
abbrev WkWf (Γ : List Tm) : Prop := ∀ {n : Nat} {Γ' : List Tm}, Ins n Γ Γ' → Wf Γ'

/-- Motive for typings. -/
abbrev WkTy (Γ : List Tm) (t A : Tm) : Prop :=
  ∀ {n : Nat} {Γ' : List Tm}, Ins n Γ Γ' → Typing Γ' (lift 1 n t) (lift 1 n A)

/-- Weakening, mutually with well-formedness of the extended context. -/
theorem weakening :
    (∀ {Γ : List Tm}, Wf Γ → WkWf Γ) ∧ (∀ {Γ : List Tm} {t A : Tm}, Typing Γ t A → WkTy Γ t A) := by
  have nil : WkWf [] := by
    intro n Γ' hins
    cases hins with
    | zero hB => exact Wf.cons Wf.nil hB
  have cons : ∀ {Γ : List Tm} {A : Tm} {s : Srt}, Wf Γ → Typing Γ A (.srt s) →
      WkWf Γ → WkTy Γ A (.srt s) → WkWf (A :: Γ) := by
    intro Γ A s hΓ hA ihΓ ihA n Γ' hins
    cases hins with
    | zero hB => exact Wf.cons (Wf.cons hΓ hA) hB
    | succ hins' => exact Wf.cons (ihΓ hins') (ihA hins')
  have srt : ∀ {Γ : List Tm} {s s' : Srt}, Wf Γ → Ax s s' → WkWf Γ → WkTy Γ (.srt s) (.srt s') := by
    intro Γ s s' _ hax ih n Γ' hins
    exact Typing.srt (ih hins) hax
  have var : ∀ {Γ : List Tm} {i : Nat} {A : Tm}, Wf Γ → Γ[i]? = some A → WkWf Γ →
      WkTy Γ (.var i) (lift (i + 1) 0 A) := by
    intro Γ i A _ hget ih n Γ' hins
    by_cases hi : i < n
    · have hget' := hins.get_lt hi hget
      have this := Typing.var (ih hins) hget'
      simp only [lift]
      rw [if_pos hi]
      rw [lift_lift_permute (i + 1) 1 0 (n - 1 - i) A (Nat.zero_le _),
        show n - 1 - i + (i + 1) = n by omega] at this
      exact this
    · have hget' := hins.get_ge (by omega) hget
      have this := Typing.var (ih hins) hget'
      simp only [lift]
      rw [if_neg hi]
      rw [lift_lift_merge (i + 1) 1 0 n A (Nat.zero_le _) (by omega)]
      exact this
  have pi : ∀ {Γ : List Tm} {A B : Tm} {s₁ s₂ s₃ : Srt}, Typing Γ A (.srt s₁) →
      Typing (A :: Γ) B (.srt s₂) → Rl s₁ s₂ s₃ → WkTy Γ A (.srt s₁) → WkTy (A :: Γ) B (.srt s₂) →
      WkTy Γ (.pi A B) (.srt s₃) := by
    intro Γ A B s₁ s₂ s₃ _ _ hrl ihA ihB n Γ' hins
    simp only [lift]
    exact Typing.pi (ihA hins) (ihB (Ins.succ hins)) hrl
  have lam : ∀ {Γ : List Tm} {A B b : Tm} {s : Srt}, Typing Γ (.pi A B) (.srt s) →
      Typing (A :: Γ) b B → WkTy Γ (.pi A B) (.srt s) → WkTy (A :: Γ) b B →
      WkTy Γ (.lam A b) (.pi A B) := by
    intro Γ A B b s _ _ ihpi ihb n Γ' hins
    have h1 := ihpi hins
    simp only [lift] at h1 ⊢
    exact Typing.lam h1 (ihb (Ins.succ hins))
  have app : ∀ {Γ : List Tm} {f a A B : Tm}, Typing Γ f (.pi A B) → Typing Γ a A →
      WkTy Γ f (.pi A B) → WkTy Γ a A → WkTy Γ (.app f a) (subst 0 a B) := by
    intro Γ f a A B _ _ ihf iha n Γ' hins
    have h1 := ihf hins
    simp only [lift] at h1 ⊢
    rw [lift_subst_distr 1 n 0 a B (Nat.zero_le _), Nat.sub_zero]
    exact Typing.app h1 (iha hins)
  have conv : ∀ {Γ : List Tm} {t A B : Tm} {s : Srt}, Typing Γ t A → Typing Γ B (.srt s) →
      Conv A B → WkTy Γ t A → WkTy Γ B (.srt s) → WkTy Γ t B := by
    intro Γ t A B s _ _ hconv iht ihB n Γ' hins
    exact Typing.conv (iht hins) (ihB hins) (hconv.lift 1 n)
  exact ⟨fun hΓ => Wf.rec (motive_1 := fun Γ _ => WkWf Γ) (motive_2 := fun Γ t A _ => WkTy Γ t A)
      nil cons srt var pi lam app conv hΓ,
    fun ht => Typing.rec (motive_1 := fun Γ _ => WkWf Γ) (motive_2 := fun Γ t A _ => WkTy Γ t A)
      nil cons srt var pi lam app conv ht⟩

/-- Single-step weakening at the head of the context. -/
theorem Typing.weaken {Γ : List Tm} {t A B : Tm} {s : Srt} (ht : Typing Γ t A)
    (hB : Typing Γ B (.srt s)) : Typing (B :: Γ) (lift 1 0 t) (lift 1 0 A) :=
  weakening.2 ht (Ins.zero hB)

theorem Wf.of_cons {Γ : List Tm} {A : Tm} (h : Wf (A :: Γ)) : Wf Γ ∧ ∃ s, Typing Γ A (.srt s) := by
  cases h with
  | cons hΓ hA => exact ⟨hΓ, _, hA⟩

/-- Every typing has a well-formed context. -/
theorem Typing.wf {Γ : List Tm} {t A : Tm} (h : Typing Γ t A) : Wf Γ :=
  Typing.rec (motive_1 := fun _ _ => True) (motive_2 := fun Γ _ _ _ => Wf Γ)
    trivial (fun _ _ _ _ => trivial) (fun hΓ _ _ => hΓ) (fun hΓ _ _ => hΓ)
    (fun _ _ _ ihA _ => ihA) (fun _ _ ihpi _ => ihpi) (fun _ _ ihf _ => ihf)
    (fun _ _ _ iht _ => iht) h

/-- The type of a variable is well typed: `Wf Γ → Γ[i]? = some A → ∃ s, Typing Γ (lift (i+1) 0 A) (srt s)`. -/
theorem Wf.get_typed : ∀ {Γ : List Tm}, Wf Γ → ∀ {i : Nat} {A : Tm}, Γ[i]? = some A →
    ∃ s, Typing Γ (lift (i + 1) 0 A) (.srt s)
  | [], _, _, _, hget => by simp at hget
  | B :: Γ, hΓ, i, A, hget => by
    obtain ⟨hΓ', s, hB⟩ := hΓ.of_cons
    cases i with
    | zero =>
      simp at hget; subst hget
      exact ⟨s, by simpa [lift] using hB.weaken hB⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      obtain ⟨s', hs'⟩ := Wf.get_typed hΓ' hget
      refine ⟨s', ?_⟩
      have := hs'.weaken hB
      rw [lift_lift_merge (i + 1) 1 0 0 A (Nat.zero_le _) (Nat.zero_le _)] at this
      simpa [lift] using this

end LeanEval.ProgramVerification.CoCStrongNormalization
