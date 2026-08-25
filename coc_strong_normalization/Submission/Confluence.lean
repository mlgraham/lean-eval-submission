import ChallengeDeps
import Mathlib.Logic.Relation
import Submission.Syntax

/-!
# Confluence of beta reduction and consequences for `Conv`

Tait–Martin-Löf: parallel reduction `Par`, stable under `lift` and `subst`, has the diamond
property via complete developments (`cd`, the triangle property `Par t t' → Par t' (cd t)`).
Hence `Steps := ReflTransGen Step` is confluent (Church–Rosser), so `Conv t u` iff `t` and `u`
have a common reduct. Consequences: Π-injectivity through `Conv`, sorts are convertible only to
themselves, and a Π is never convertible to a sort.
-/

namespace LeanEval.ProgramVerification.CoCStrongNormalization

open Submission.Syntax

/-- Multi-step reduction. -/
abbrev Steps : Tm → Tm → Prop := Relation.ReflTransGen Step

/-! ### Parallel reduction -/

inductive Par : Tm → Tm → Prop where
  | var (i : Nat) : Par (.var i) (.var i)
  | srt (s : Srt) : Par (.srt s) (.srt s)
  | app {f f' a a' : Tm} : Par f f' → Par a a' → Par (.app f a) (.app f' a')
  | lam {A A' b b' : Tm} : Par A A' → Par b b' → Par (.lam A b) (.lam A' b')
  | pi {A A' B B' : Tm} : Par A A' → Par B B' → Par (.pi A B) (.pi A' B')
  | beta (A : Tm) {b b' a a' : Tm} : Par b b' → Par a a' →
      Par (.app (.lam A b) a) (subst 0 a' b')

theorem Par.refl : ∀ t : Tm, Par t t
  | .var i => .var i
  | .srt s => .srt s
  | .app f a => .app (Par.refl f) (Par.refl a)
  | .lam A b => .lam (Par.refl A) (Par.refl b)
  | .pi A B => .pi (Par.refl A) (Par.refl B)

theorem Step.par {t t' : Tm} (h : Step t t') : Par t t' := by
  induction h with
  | beta A b a => exact Par.beta A (Par.refl b) (Par.refl a)
  | appFun a _ ih => exact Par.app ih (Par.refl a)
  | appArg f _ ih => exact Par.app (Par.refl f) ih
  | lamTy b _ ih => exact Par.lam ih (Par.refl b)
  | lamBody A _ ih => exact Par.lam (Par.refl A) ih
  | piDom B _ ih => exact Par.pi ih (Par.refl B)
  | piCod A _ ih => exact Par.pi (Par.refl A) ih

/-! ### Congruence of `Steps` -/

/-- Map a multi-step reduction through a `Step`-preserving function. -/
theorem Steps.map {t u : Tm} (h : Steps t u) (g : Tm → Tm)
    (hg : ∀ x y, Step x y → Step (g x) (g y)) : Steps (g t) (g u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (hg _ _ hstep)

theorem Steps.app {f f' a a' : Tm} (hf : Steps f f') (ha : Steps a a') :
    Steps (.app f a) (.app f' a') := by
  refine Relation.ReflTransGen.trans (b := Tm.app f' a) ?_ ?_
  · exact hf.map (fun x => Tm.app x a) (fun _ _ h => Step.appFun a h)
  · exact ha.map (fun x => Tm.app f' x) (fun _ _ h => Step.appArg f' h)

theorem Steps.lam {A A' b b' : Tm} (hA : Steps A A') (hb : Steps b b') :
    Steps (.lam A b) (.lam A' b') := by
  refine Relation.ReflTransGen.trans (b := Tm.lam A' b) ?_ ?_
  · exact hA.map (fun x => Tm.lam x b) (fun _ _ h => Step.lamTy b h)
  · exact hb.map (fun x => Tm.lam A' x) (fun _ _ h => Step.lamBody A' h)

theorem Steps.pi {A A' B B' : Tm} (hA : Steps A A') (hB : Steps B B') :
    Steps (.pi A B) (.pi A' B') := by
  refine Relation.ReflTransGen.trans (b := Tm.pi A' B) ?_ ?_
  · exact hA.map (fun x => Tm.pi x B) (fun _ _ h => Step.piDom B h)
  · exact hB.map (fun x => Tm.pi A' x) (fun _ _ h => Step.piCod A' h)

theorem Par.steps {t t' : Tm} (h : Par t t') : Steps t t' := by
  induction h with
  | var i => exact Relation.ReflTransGen.refl
  | srt s => exact Relation.ReflTransGen.refl
  | app _ _ ihf iha => exact Steps.app ihf iha
  | lam _ _ ihA ihb => exact Steps.lam ihA ihb
  | pi _ _ ihA ihB => exact Steps.pi ihA ihB
  | beta A _ _ ihb iha =>
    exact Relation.ReflTransGen.tail (Steps.app (Steps.lam Relation.ReflTransGen.refl ihb) iha)
      (Step.beta A _ _)

/-! ### `Par` is stable under `lift` and `subst` -/

theorem Par.lift {t t' : Tm} (h : Par t t') (d c : Nat) : Par (lift d c t) (lift d c t') := by
  induction h generalizing c with
  | var i => simp only [LeanEval.ProgramVerification.CoCStrongNormalization.lift]; split_ifs <;> exact Par.var _
  | srt s => exact Par.srt s
  | app _ _ ihf iha => exact Par.app (ihf c) (iha c)
  | lam _ _ ihA ihb => exact Par.lam (ihA c) (ihb (c + 1))
  | pi _ _ ihA ihB => exact Par.pi (ihA c) (ihB (c + 1))
  | beta A _ _ ihb iha =>
    simp only [LeanEval.ProgramVerification.CoCStrongNormalization.lift]
    rw [lift_subst_distr d c 0 _ _ (Nat.zero_le _), Nat.sub_zero]
    exact Par.beta _ (ihb (c + 1)) (iha c)

theorem Par.subst {t t' u u' : Tm} (h : Par t t') (hu : Par u u') (k : Nat) :
    Par (subst k u t) (subst k u' t') := by
  induction h generalizing k with
  | var i =>
    simp only [LeanEval.ProgramVerification.CoCStrongNormalization.subst]
    split_ifs
    · exact Par.var _
    · exact hu.lift k 0
    · exact Par.var _
  | srt s => exact Par.srt s
  | app _ _ ihf iha => exact Par.app (ihf k) (iha k)
  | lam _ _ ihA ihb => exact Par.lam (ihA k) (ihb (k + 1))
  | pi _ _ ihA ihB => exact Par.pi (ihA k) (ihB (k + 1))
  | beta A _ _ ihb iha =>
    simp only [LeanEval.ProgramVerification.CoCStrongNormalization.subst]
    rw [subst_subst_distr 0 k _ _ _ (Nat.zero_le _), Nat.sub_zero]
    exact Par.beta _ (ihb (k + 1)) (iha k)

/-! ### Complete developments and the diamond property -/

/-- The complete development of a term: contract every redex present. -/
def cd : Tm → Tm
  | .var i => .var i
  | .srt s => .srt s
  | .app (.lam _ b) a => subst 0 (cd a) (cd b)
  | .app f a => .app (cd f) (cd a)
  | .lam A b => .lam (cd A) (cd b)
  | .pi A B => .pi (cd A) (cd B)

theorem Par.lam_inv {A b t' : Tm} (h : Par (.lam A b) t') :
    ∃ A' b', t' = .lam A' b' ∧ Par A A' ∧ Par b b' := by
  cases h with
  | lam hA hb => exact ⟨_, _, rfl, hA, hb⟩

/-- The triangle property: every parallel reduct of `t` parallel-reduces to `cd t`. -/
theorem Par.triangle {t t' : Tm} (h : Par t t') : Par t' (cd t) := by
  induction h with
  | var i => exact Par.var i
  | srt s => exact Par.srt s
  | app hf ha ihf iha =>
    rename_i f f' a a'
    cases f with
    | lam A b =>
      obtain ⟨A', b', rfl, hA, hb⟩ := Par.lam_inv hf
      -- `ihf : Par (lam A' b') (cd (lam A b))`
      simp only [cd] at ihf ⊢
      obtain ⟨_, _, heq, _, hb'⟩ := Par.lam_inv ihf
      cases heq
      exact Par.beta A' hb' iha
    | var i => simp only [cd]; exact Par.app ihf iha
    | srt s => simp only [cd]; exact Par.app ihf iha
    | app g c => simp only [cd]; exact Par.app ihf iha
    | pi A B => simp only [cd]; exact Par.app ihf iha
  | lam _ _ ihA ihb => simp only [cd]; exact Par.lam ihA ihb
  | pi _ _ ihA ihB => simp only [cd]; exact Par.pi ihA ihB
  | beta A _ _ ihb iha =>
    simp only [cd]
    exact Par.subst ihb iha 0

theorem Par.diamond {t u v : Tm} (hu : Par t u) (hv : Par t v) : ∃ w, Par u w ∧ Par v w :=
  ⟨cd t, hu.triangle, hv.triangle⟩

/-! ### Church–Rosser -/

/-- Multi-step parallel reduction. -/
abbrev Pars : Tm → Tm → Prop := Relation.ReflTransGen Par

theorem Pars.strip {t u v : Tm} (hu : Par t u) (hv : Pars t v) : ∃ w, Pars u w ∧ Par v w := by
  induction hv generalizing u with
  | refl => exact ⟨u, Relation.ReflTransGen.refl, hu⟩
  | tail _ hstep ih =>
    obtain ⟨w, hw₁, hw₂⟩ := ih hu
    obtain ⟨w', hw'₁, hw'₂⟩ := Par.diamond hw₂ hstep
    exact ⟨w', Relation.ReflTransGen.tail hw₁ hw'₁, hw'₂⟩

theorem Pars.confluent {t u v : Tm} (hu : Pars t u) (hv : Pars t v) :
    ∃ w, Pars u w ∧ Pars v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
    obtain ⟨w, hw₁, hw₂⟩ := ih hv
    obtain ⟨w', hw'₁, hw'₂⟩ := Pars.strip hstep hw₁
    exact ⟨w', hw'₁, Relation.ReflTransGen.tail hw₂ hw'₂⟩

theorem Steps.pars {t u : Tm} (h : Steps t u) : Pars t u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih hstep.par

/-- Map a multi-step reduction through a `Par`-preserving function. -/
theorem Steps.map_par {t u : Tm} (h : Steps t u) (g : Tm → Tm)
    (hg : ∀ x y, Step x y → Par (g x) (g y)) : Steps (g t) (g u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.trans ih (hg _ _ hstep).steps

theorem Pars.steps {t u : Tm} (h : Pars t u) : Steps t u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.trans ih hstep.steps

/-- **Church–Rosser.** -/
theorem Steps.confluent {t u v : Tm} (hu : Steps t u) (hv : Steps t v) :
    ∃ w, Steps u w ∧ Steps v w := by
  obtain ⟨w, hw₁, hw₂⟩ := Pars.confluent hu.pars hv.pars
  exact ⟨w, hw₁.steps, hw₂.steps⟩

/-! ### `Conv` as joinability -/

theorem Steps.conv {t u : Tm} (h : Steps t u) : Conv t u := by
  induction h with
  | refl => exact Conv.refl _
  | tail _ hstep ih => exact Conv.fwd ih hstep

/-- Prepend a backward step: `Conv u t → Step u v → Conv v t`. -/
theorem Conv.head_bwd {u t v : Tm} (h : Conv u t) (hs : Step u v) : Conv v t := by
  induction h with
  | refl => exact Conv.bwd (Conv.refl _) hs
  | fwd _ hstep ih => exact Conv.fwd ih hstep
  | bwd _ hstep ih => exact Conv.bwd ih hstep

/-- Prepend a forward step: `Conv u t → Step v u → Conv v t`. -/
theorem Conv.head_fwd {u t v : Tm} (h : Conv u t) (hs : Step v u) : Conv v t := by
  induction h with
  | refl => exact Conv.fwd (Conv.refl _) hs
  | fwd _ hstep ih => exact Conv.fwd ih hstep
  | bwd _ hstep ih => exact Conv.bwd ih hstep

theorem Conv.symm {t u : Tm} (h : Conv t u) : Conv u t := by
  induction h with
  | refl => exact Conv.refl _
  | fwd _ hstep ih => exact Conv.head_bwd ih hstep
  | bwd _ hstep ih => exact Conv.head_fwd ih hstep

theorem Conv.trans {t u v : Tm} (h₁ : Conv t u) (h₂ : Conv u v) : Conv t v := by
  induction h₂ with
  | refl => exact h₁
  | fwd _ hstep ih => exact Conv.fwd ih hstep
  | bwd _ hstep ih => exact Conv.bwd ih hstep

/-- `Conv t u` iff `t` and `u` have a common reduct. -/
theorem Conv.joinable {t u : Tm} (h : Conv t u) : ∃ v, Steps t v ∧ Steps u v := by
  induction h with
  | refl => exact ⟨_, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | fwd _ hstep ih =>
    obtain ⟨w, hw₁, hw₂⟩ := ih
    obtain ⟨w', hw'₁, hw'₂⟩ := Steps.confluent hw₂ (Relation.ReflTransGen.single hstep)
    exact ⟨w', Relation.ReflTransGen.trans hw₁ hw'₁, hw'₂⟩
  | bwd _ hstep ih =>
    obtain ⟨w, hw₁, hw₂⟩ := ih
    exact ⟨w, hw₁, Relation.ReflTransGen.head hstep hw₂⟩

theorem Conv.of_joinable {t u v : Tm} (h₁ : Steps t v) (h₂ : Steps u v) : Conv t u :=
  Conv.trans h₁.conv h₂.conv.symm

/-! ### Shape lemmas for reducts -/

theorem Steps.pi_inv {A B v : Tm} (h : Steps (.pi A B) v) :
    ∃ A' B', v = .pi A' B' ∧ Steps A A' ∧ Steps B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
    obtain ⟨A', B', rfl, hA, hB⟩ := ih
    cases hstep with
    | piDom _ h => exact ⟨_, _, rfl, Relation.ReflTransGen.tail hA h, hB⟩
    | piCod _ h => exact ⟨_, _, rfl, hA, Relation.ReflTransGen.tail hB h⟩

theorem Steps.srt_inv {s : Srt} {v : Tm} (h : Steps (.srt s) v) : v = .srt s := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => subst ih; cases hstep

/-- **Π-injectivity.** -/
theorem Conv.pi_inj {A B A' B' : Tm} (h : Conv (.pi A B) (.pi A' B')) :
    Conv A A' ∧ Conv B B' := by
  obtain ⟨v, h₁, h₂⟩ := h.joinable
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := h₁.pi_inv
  obtain ⟨A₂, B₂, heq, hA₂, hB₂⟩ := h₂.pi_inv
  cases heq
  exact ⟨Conv.of_joinable hA₁ hA₂, Conv.of_joinable hB₁ hB₂⟩

theorem Conv.srt_inj {s s' : Srt} (h : Conv (.srt s) (.srt s')) : s = s' := by
  obtain ⟨v, h₁, h₂⟩ := h.joinable
  have e₁ := h₁.srt_inv
  have e₂ := h₂.srt_inv
  subst e₁
  cases e₂
  rfl

theorem Conv.pi_srt {A B : Tm} {s : Srt} (h : Conv (.pi A B) (.srt s)) : False := by
  obtain ⟨v, h₁, h₂⟩ := h.joinable
  obtain ⟨A₁, B₁, rfl, -, -⟩ := h₁.pi_inv
  cases h₂.srt_inv

/-! ### `Conv` is a congruence, and compatible with `subst`/`lift` -/

theorem Conv.subst_left {A A' u : Tm} (h : Conv A A') (k : Nat) :
    Conv (subst k u A) (subst k u A') := by
  obtain ⟨v, h₁, h₂⟩ := h.joinable
  refine Conv.of_joinable (v := subst k u v) ?_ ?_
  · exact h₁.map_par (fun x => subst k u x) (fun _ _ hs => Par.subst hs.par (Par.refl u) k)
  · exact h₂.map_par (fun x => subst k u x) (fun _ _ hs => Par.subst hs.par (Par.refl u) k)

theorem Conv.subst_right {B a a' : Tm} (h : Conv a a') (k : Nat) :
    Conv (subst k a B) (subst k a' B) := by
  obtain ⟨v, h₁, h₂⟩ := h.joinable
  refine Conv.of_joinable (v := subst k v B) ?_ ?_
  · exact h₁.map_par (fun x => subst k x B) (fun _ _ hs => Par.subst (Par.refl B) hs.par k)
  · exact h₂.map_par (fun x => subst k x B) (fun _ _ hs => Par.subst (Par.refl B) hs.par k)

theorem Conv.lift {A A' : Tm} (h : Conv A A') (d c : Nat) :
    Conv (lift d c A) (lift d c A') := by
  obtain ⟨v, h₁, h₂⟩ := h.joinable
  refine Conv.of_joinable (v := LeanEval.ProgramVerification.CoCStrongNormalization.lift d c v) ?_ ?_
  · exact h₁.map_par (fun x => LeanEval.ProgramVerification.CoCStrongNormalization.lift d c x) (fun _ _ hs => hs.par.lift d c)
  · exact h₂.map_par (fun x => LeanEval.ProgramVerification.CoCStrongNormalization.lift d c x) (fun _ _ hs => hs.par.lift d c)

theorem Conv.pi_congr {A A' B B' : Tm} (hA : Conv A A') (hB : Conv B B') :
    Conv (.pi A B) (.pi A' B') := by
  obtain ⟨vA, hA₁, hA₂⟩ := hA.joinable
  obtain ⟨vB, hB₁, hB₂⟩ := hB.joinable
  exact Conv.of_joinable (Steps.pi hA₁ hB₁) (Steps.pi hA₂ hB₂)

end LeanEval.ProgramVerification.CoCStrongNormalization
