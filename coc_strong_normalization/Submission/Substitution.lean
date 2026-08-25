import ChallengeDeps
import Mathlib.Tactic.SplitIfs
import Submission.Syntax
import Submission.Confluence
import Submission.Weakening

/-!
# The substitution lemma

`Sub n Γ Γ' a` says `Γ'` is obtained from `Γ` by removing the binding at depth `n` (of type `A`)
and substituting `a : A` into the `n` more recent bindings. Substitution:
`Typing Γ t B → Sub n Γ Γ' a → Typing Γ' (subst n a t) (subst n a B)`, mutually with
`Wf Γ → Sub n Γ Γ' a → Wf Γ'`.
-/

namespace LeanEval.ProgramVerification.CoCStrongNormalization

open Submission.Syntax

/-- Substitution of `a` for the binding at depth `n`. -/
inductive Sub : Nat → List Tm → List Tm → Tm → Prop where
  | zero {Γ : List Tm} {A a : Tm} : Typing Γ a A → Sub 0 (A :: Γ) Γ a
  | succ {n : Nat} {Γ Γ' : List Tm} {a C : Tm} :
      Sub n Γ Γ' a → Sub (n + 1) (C :: Γ) (subst n a C :: Γ') a

theorem Sub.get_lt {n : Nat} {Γ Γ' : List Tm} {a : Tm} (h : Sub n Γ Γ' a) {i : Nat} {C : Tm}
    (hi : i < n) (hget : Γ[i]? = some C) : Γ'[i]? = some (subst (n - 1 - i) a C) := by
  induction h generalizing i with
  | zero _ => omega
  | succ _ ih =>
    cases i with
    | zero => simp at hget ⊢; subst hget; simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget ⊢
      rw [ih (by omega) hget]
      congr 2; omega

theorem Sub.get_gt {n : Nat} {Γ Γ' : List Tm} {a : Tm} (h : Sub n Γ Γ' a) {i : Nat} {C : Tm}
    (hi : n < i) (hget : Γ[i]? = some C) : Γ'[i - 1]? = some C := by
  induction h generalizing i with
  | zero _ =>
    cases i with
    | zero => omega
    | succ i => simpa using hget
  | succ _ ih =>
    cases i with
    | zero => omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      cases i with
      | zero => omega
      | succ i =>
        have := ih (by omega) hget
        simpa using this

/-- The substituted term is well typed, lifted to the depth of the substitution. -/
theorem Sub.get_eq {n : Nat} {Γ Γ' : List Tm} {a : Tm} (h : Sub n Γ Γ' a) (hΓ' : Wf Γ')
    {C : Tm} (hget : Γ[n]? = some C) : Typing Γ' (lift n 0 a) (lift n 0 C) := by
  induction h with
  | zero ha =>
    simp at hget; subst hget
    simpa using ha
  | succ _ ih =>
    simp only [List.getElem?_cons_succ] at hget
    obtain ⟨hΓ'', s, hC'⟩ := hΓ'.of_cons
    have := (ih hΓ'' hget).weaken hC'
    rw [lift_lift_merge _ 1 0 0 _ (Nat.zero_le _) (Nat.zero_le _),
      lift_lift_merge _ 1 0 0 _ (Nat.zero_le _) (Nat.zero_le _)] at this
    exact this

/-- Motive for contexts. -/
abbrev SbWf (Γ : List Tm) : Prop := ∀ {n : Nat} {Γ' : List Tm} {a : Tm}, Sub n Γ Γ' a → Wf Γ'

/-- Motive for typings. -/
abbrev SbTy (Γ : List Tm) (t B : Tm) : Prop :=
  ∀ {n : Nat} {Γ' : List Tm} {a : Tm}, Sub n Γ Γ' a → Typing Γ' (subst n a t) (subst n a B)

/-- The substitution lemma, mutually with well-formedness. -/
theorem substitution :
    (∀ {Γ : List Tm}, Wf Γ → SbWf Γ) ∧ (∀ {Γ : List Tm} {t B : Tm}, Typing Γ t B → SbTy Γ t B) := by
  have nil : SbWf [] := by
    intro n Γ' a hsub
    cases hsub
  have cons : ∀ {Γ : List Tm} {A : Tm} {s : Srt}, Wf Γ → Typing Γ A (.srt s) →
      SbWf Γ → SbTy Γ A (.srt s) → SbWf (A :: Γ) := by
    intro Γ A s hΓ _ ihΓ ihA n Γ' a hsub
    cases hsub with
    | zero _ => exact hΓ
    | succ hsub' =>
      have := ihA hsub'
      simp only [subst] at this
      exact Wf.cons (ihΓ hsub') this
  have srt : ∀ {Γ : List Tm} {s s' : Srt}, Wf Γ → Ax s s' → SbWf Γ → SbTy Γ (.srt s) (.srt s') := by
    intro Γ s s' _ hax ih n Γ' a hsub
    simp only [subst]
    exact Typing.srt (ih hsub) hax
  have var : ∀ {Γ : List Tm} {i : Nat} {A : Tm}, Wf Γ → Γ[i]? = some A → SbWf Γ →
      SbTy Γ (.var i) (lift (i + 1) 0 A) := by
    intro Γ i A _ hget ih n Γ' a hsub
    have hΓ' := ih hsub
    simp only [subst]
    by_cases h1 : i < n
    · rw [if_pos h1]
      have hget' := hsub.get_lt h1 hget
      have this := Typing.var hΓ' hget'
      -- `subst n a (lift (i+1) 0 A) = lift (i+1) 0 (subst (n-1-i) a A)`
      rw [subst_lift_comm (i + 1) 0 n a A (by omega), show n - (i + 1) = n - 1 - i by omega]
      exact this
    · rw [if_neg h1]
      by_cases h2 : i = n
      · rw [if_pos h2]
        subst h2
        have this := hsub.get_eq hΓ' hget
        -- `subst i a (lift (i+1) 0 A) = lift i 0 A`
        rw [subst_lift_cancel (i + 1) 0 i a A (Nat.zero_le _) (by omega), Nat.add_sub_cancel]
        exact this
      · rw [if_neg h2]
        have hget' := hsub.get_gt (by omega) hget
        have this := Typing.var hΓ' hget'
        rw [subst_lift_cancel (i + 1) 0 n a A (Nat.zero_le _) (by omega), Nat.add_sub_cancel]
        rw [show i - 1 + 1 = i by omega] at this
        exact this
  have pi : ∀ {Γ : List Tm} {A B : Tm} {s₁ s₂ s₃ : Srt}, Typing Γ A (.srt s₁) →
      Typing (A :: Γ) B (.srt s₂) → Rl s₁ s₂ s₃ → SbTy Γ A (.srt s₁) → SbTy (A :: Γ) B (.srt s₂) →
      SbTy Γ (.pi A B) (.srt s₃) := by
    intro Γ A B s₁ s₂ s₃ _ _ hrl ihA ihB n Γ' a hsub
    have h1 := ihA hsub
    have h2 := ihB (Sub.succ hsub)
    simp only [subst] at h1 h2 ⊢
    exact Typing.pi h1 h2 hrl
  have lam : ∀ {Γ : List Tm} {A B b : Tm} {s : Srt}, Typing Γ (.pi A B) (.srt s) →
      Typing (A :: Γ) b B → SbTy Γ (.pi A B) (.srt s) → SbTy (A :: Γ) b B →
      SbTy Γ (.lam A b) (.pi A B) := by
    intro Γ A B b s _ _ ihpi ihb n Γ' a hsub
    have h1 := ihpi hsub
    have h2 := ihb (Sub.succ hsub)
    simp only [subst] at h1 h2 ⊢
    exact Typing.lam h1 h2
  have app : ∀ {Γ : List Tm} {f a A B : Tm}, Typing Γ f (.pi A B) → Typing Γ a A →
      SbTy Γ f (.pi A B) → SbTy Γ a A → SbTy Γ (.app f a) (subst 0 a B) := by
    intro Γ f a A B _ _ ihf iha n Γ' u hsub
    have h1 := ihf hsub
    have h2 := iha hsub
    simp only [subst] at h1 ⊢
    rw [subst_subst_distr 0 n u a B (Nat.zero_le _), Nat.sub_zero]
    exact Typing.app h1 h2
  have conv : ∀ {Γ : List Tm} {t A B : Tm} {s : Srt}, Typing Γ t A → Typing Γ B (.srt s) →
      Conv A B → SbTy Γ t A → SbTy Γ B (.srt s) → SbTy Γ t B := by
    intro Γ t A B s _ _ hconv iht ihB n Γ' a hsub
    have h2 := ihB hsub
    simp only [subst] at h2
    exact Typing.conv (iht hsub) h2 (hconv.subst_left n)
  exact ⟨fun hΓ => Wf.rec (motive_1 := fun Γ _ => SbWf Γ) (motive_2 := fun Γ t B _ => SbTy Γ t B)
      nil cons srt var pi lam app conv hΓ,
    fun ht => Typing.rec (motive_1 := fun Γ _ => SbWf Γ) (motive_2 := fun Γ t B _ => SbTy Γ t B)
      nil cons srt var pi lam app conv ht⟩

/-- Substitution at the head of the context. -/
theorem Typing.subst0 {Γ : List Tm} {A B b a : Tm} (hb : Typing (A :: Γ) b B)
    (ha : Typing Γ a A) : Typing Γ (subst 0 a b) (subst 0 a B) :=
  substitution.2 hb (Sub.zero ha)

end LeanEval.ProgramVerification.CoCStrongNormalization
