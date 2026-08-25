import ChallengeDeps
import Mathlib.Tactic.SplitIfs
import Submission.Syntax
import Submission.Confluence
import Submission.Weakening
import Submission.Substitution

/-!
# Generation lemmas, type correctness, context conversion, subject reduction
-/

namespace LeanEval.ProgramVerification.CoCStrongNormalization

open Submission.Syntax

/-- `subst k (var 0) (lift 1 (k+1) t) = t`: substituting the variable back after lifting past it. -/
theorem subst_var_lift (k : Nat) (t : Tm) : subst k (.var 0) (lift 1 (k + 1) t) = t := by
  induction t generalizing k with
  | var i =>
    simp only [lift, subst]
    split_ifs <;> (try simp only [lift, subst]) <;> (try split_ifs) <;>
      first | rfl | (exfalso; omega) | (congr 1; omega)
  | srt s => rfl
  | app f a ihf iha => simp [lift, subst, ihf k, iha k]
  | lam A b ihA ihb => simp [lift, subst, ihA k, ihb (k + 1)]
  | pi A B ihA ihB => simp [lift, subst, ihA k, ihB (k + 1)]

/-- Every sort has a sort. -/
theorem Ax.exists_above (s : Srt) : ∃ s', Ax s s' := by
  cases s with
  | prop => exact ⟨_, Ax.prop⟩
  | type i => exact ⟨_, Ax.type i⟩

/-! ### Generation lemmas -/

theorem Typing.gen_srt {Γ : List Tm} {s : Srt} {T : Tm} (h : Typing Γ (.srt s) T) :
    ∃ s', Ax s s' ∧ Conv (.srt s') T := by
  refine Typing.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun Γ t T _ => ∀ s, t = .srt s → ∃ s', Ax s s' ∧ Conv (.srt s') T)
    trivial (fun _ _ _ _ => trivial) ?_ ?_ ?_ ?_ ?_ ?_ h s rfl
  · intro Γ s s' _ hax _ s₀ heq; cases heq; exact ⟨s', hax, Conv.refl _⟩
  · intro _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro Γ t A B s _ _ hconv ih _ s₀ heq
    obtain ⟨s', hax, hc⟩ := ih s₀ heq
    exact ⟨s', hax, hc.trans hconv⟩

theorem Typing.gen_var {Γ : List Tm} {i : Nat} {T : Tm} (h : Typing Γ (.var i) T) :
    ∃ A, Γ[i]? = some A ∧ Conv (lift (i + 1) 0 A) T := by
  refine Typing.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun Γ t T _ => ∀ i, t = .var i → ∃ A, Γ[i]? = some A ∧ Conv (lift (i + 1) 0 A) T)
    trivial (fun _ _ _ _ => trivial) ?_ ?_ ?_ ?_ ?_ ?_ h i rfl
  · intro _ _ _ _ _ _ _ heq; cases heq
  · intro Γ i A _ hget _ i₀ heq; cases heq; exact ⟨A, hget, Conv.refl _⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro Γ t A B s _ _ hconv ih _ i₀ heq
    obtain ⟨A₀, hget, hc⟩ := ih i₀ heq
    exact ⟨A₀, hget, hc.trans hconv⟩

theorem Typing.gen_pi {Γ : List Tm} {A B T : Tm} (h : Typing Γ (.pi A B) T) :
    ∃ s₁ s₂ s₃, Typing Γ A (.srt s₁) ∧ Typing (A :: Γ) B (.srt s₂) ∧ Rl s₁ s₂ s₃ ∧
      Conv (.srt s₃) T := by
  refine Typing.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun Γ t T _ => ∀ A B, t = .pi A B → ∃ s₁ s₂ s₃, Typing Γ A (.srt s₁) ∧
      Typing (A :: Γ) B (.srt s₂) ∧ Rl s₁ s₂ s₃ ∧ Conv (.srt s₃) T)
    trivial (fun _ _ _ _ => trivial) ?_ ?_ ?_ ?_ ?_ ?_ h A B rfl
  · intro _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ heq; cases heq
  · intro Γ A B s₁ s₂ s₃ hA hB hrl _ _ A₀ B₀ heq; cases heq
    exact ⟨s₁, s₂, s₃, hA, hB, hrl, Conv.refl _⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro Γ t A B s _ _ hconv ih _ A₀ B₀ heq
    obtain ⟨s₁, s₂, s₃, hA, hB, hrl, hc⟩ := ih A₀ B₀ heq
    exact ⟨s₁, s₂, s₃, hA, hB, hrl, hc.trans hconv⟩

theorem Typing.gen_lam {Γ : List Tm} {A b T : Tm} (h : Typing Γ (.lam A b) T) :
    ∃ B s, Typing Γ (.pi A B) (.srt s) ∧ Typing (A :: Γ) b B ∧ Conv (.pi A B) T := by
  refine Typing.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun Γ t T _ => ∀ A b, t = .lam A b → ∃ B s, Typing Γ (.pi A B) (.srt s) ∧
      Typing (A :: Γ) b B ∧ Conv (.pi A B) T)
    trivial (fun _ _ _ _ => trivial) ?_ ?_ ?_ ?_ ?_ ?_ h A b rfl
  · intro _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro Γ A B b s hpi hb _ _ A₀ b₀ heq; cases heq
    exact ⟨B, s, hpi, hb, Conv.refl _⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro Γ t A B s _ _ hconv ih _ A₀ b₀ heq
    obtain ⟨B₀, s₀, hpi, hb, hc⟩ := ih A₀ b₀ heq
    exact ⟨B₀, s₀, hpi, hb, hc.trans hconv⟩

theorem Typing.gen_app {Γ : List Tm} {f a T : Tm} (h : Typing Γ (.app f a) T) :
    ∃ A B, Typing Γ f (.pi A B) ∧ Typing Γ a A ∧ Conv (subst 0 a B) T := by
  refine Typing.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun Γ t T _ => ∀ f a, t = .app f a → ∃ A B, Typing Γ f (.pi A B) ∧
      Typing Γ a A ∧ Conv (subst 0 a B) T)
    trivial (fun _ _ _ _ => trivial) ?_ ?_ ?_ ?_ ?_ ?_ h f a rfl
  · intro _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro _ _ _ _ _ _ _ _ _ _ _ heq; cases heq
  · intro Γ f a A B hf ha _ _ f₀ a₀ heq; cases heq
    exact ⟨A, B, hf, ha, Conv.refl _⟩
  · intro Γ t A B s _ _ hconv ih _ f₀ a₀ heq
    obtain ⟨A₀, B₀, hf, ha, hc⟩ := ih f₀ a₀ heq
    exact ⟨A₀, B₀, hf, ha, hc.trans hconv⟩

/-! ### Type correctness -/

/-- The type of a well-typed term is itself well typed (by a sort). -/
theorem Typing.type_sort {Γ : List Tm} {t A : Tm} (h : Typing Γ t A) :
    ∃ s, Typing Γ A (.srt s) := by
  refine Typing.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun Γ t A _ => ∃ s, Typing Γ A (.srt s))
    trivial (fun _ _ _ _ => trivial) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Γ s s' hΓ _ _
    obtain ⟨s'', hax⟩ := Ax.exists_above s'
    exact ⟨s'', Typing.srt hΓ hax⟩
  · intro Γ i A hΓ hget _
    exact hΓ.get_typed hget
  · intro Γ A B s₁ s₂ s₃ hA _ _ _ _
    obtain ⟨s', hax⟩ := Ax.exists_above s₃
    exact ⟨s', Typing.srt hA.wf hax⟩
  · intro Γ A B b s hpi _ _ _
    exact ⟨s, hpi⟩
  · intro Γ f a A B hf ha ihf _
    obtain ⟨s, hs⟩ := ihf
    obtain ⟨s₁, s₂, s₃, _, hB, _, _⟩ := hs.gen_pi
    have := hB.subst0 ha
    simp only [subst] at this
    exact ⟨s₂, this⟩
  · intro Γ t A B s _ hB _ _ _
    exact ⟨s, hB⟩

/-! ### Context conversion (head binding) -/

theorem Typing.ctx_conv {Γ : List Tm} {A A' t B : Tm} {s : Srt} (ht : Typing (A :: Γ) t B)
    (hA' : Typing Γ A' (.srt s)) (hconv : Conv A A') : Typing (A' :: Γ) t B := by
  obtain ⟨hΓ, s₀, hA⟩ := ht.wf.of_cons
  -- weaken `t` by inserting `A'` below `A`
  have hw := weakening.2 ht (Ins.succ (Ins.zero hA'))
  -- `var 0 : lift 1 0 A` in `A' :: Γ`
  have hv : Typing (A' :: Γ) (.var 0) (lift 1 0 A) := by
    have h0 : Typing (A' :: Γ) (.var 0) (lift 1 0 A') := Typing.var (Wf.cons hΓ hA') rfl
    exact Typing.conv h0 (hA.weaken hA') (hconv.symm.lift 1 0)
  have hs := substitution.2 hw (Sub.zero hv)
  rw [subst_var_lift 0 t, subst_var_lift 0 B] at hs
  exact hs

/-! ### Subject reduction -/

theorem Step.conv {t t' : Tm} (h : Step t t') : Conv t t' := Conv.fwd (Conv.refl t) h

theorem subject_reduction' {Γ : List Tm} {t A : Tm} (h : Typing Γ t A) :
    ∀ t', Step t t' → Typing Γ t' A := by
  refine Typing.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun Γ t A _ => ∀ t', Step t t' → Typing Γ t' A)
    trivial (fun _ _ _ _ => trivial) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro _ _ _ _ _ _ t' hs; cases hs
  · intro _ _ _ _ _ _ t' hs; cases hs
  · intro Γ A B s₁ s₂ s₃ hA hB hrl ihA ihB t' hs
    cases hs with
    | piDom _ hA' =>
      have hA'' := ihA _ hA'
      exact Typing.pi hA'' (hB.ctx_conv hA'' hA'.conv) hrl
    | piCod _ hB' => exact Typing.pi hA (ihB _ hB') hrl
  · intro Γ A B b s hpi hb ihpi ihb t' hs
    cases hs with
    | lamTy _ hA' =>
      have hpi' := ihpi _ (Step.piDom B hA')
      obtain ⟨s₁, _, _, hA'', _, _, _⟩ := hpi'.gen_pi
      have hb' := hb.ctx_conv hA'' hA'.conv
      exact Typing.conv (Typing.lam hpi' hb') hpi (Conv.bwd (Conv.refl _) (Step.piDom B hA'))
    | lamBody _ hb' => exact Typing.lam hpi (ihb _ hb')
  · intro Γ f a A B hf ha ihf iha t' hs
    obtain ⟨s, hty⟩ := (Typing.app hf ha).type_sort
    cases hs with
    | beta A₀ b _ =>
      obtain ⟨B₀, s₀, hpi₀, hb, hc⟩ := hf.gen_lam
      obtain ⟨hcA, hcB⟩ := hc.pi_inj
      obtain ⟨s₁, _, _, hA₀, _, _, _⟩ := hpi₀.gen_pi
      have ha' : Typing Γ a A₀ := Typing.conv ha hA₀ hcA.symm
      have hsub := hb.subst0 ha'
      exact Typing.conv hsub hty (hcB.subst_left 0)
    | appFun _ hf' => exact Typing.app (ihf _ hf') ha
    | appArg _ ha' =>
      have h := Typing.app hf (iha _ ha')
      exact Typing.conv h hty ((Conv.bwd (Conv.refl _) ha').subst_right 0)
  · intro Γ t A B s _ hB hconv iht _ t' hs
    exact Typing.conv (iht _ hs) hB hconv

theorem subject_reduction (Γ : List Tm) (t t' A : Tm) :
    Typing Γ t A → Step t t' → Typing Γ t' A :=
  fun h hs => subject_reduction' h t' hs

end LeanEval.ProgramVerification.CoCStrongNormalization
