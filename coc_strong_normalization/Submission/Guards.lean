import ChallengeDeps

/-! Explicit derivations for the three anti-vacuity guards. -/

namespace Submission.Guards

open LeanEval.ProgramVerification.CoCStrongNormalization

/-- `⊢ Prop : Type 0`. -/
theorem typing_prop_nil : Typing [] (.srt .prop) (.srt (.type 0)) :=
  Typing.srt Wf.nil Ax.prop

/-- `Prop` is a well-formed context. -/
theorem wf_prop : Wf [.srt .prop] := Wf.cons Wf.nil typing_prop_nil

/-- `A : Prop ⊢ A : Prop` (the variable `0`). -/
theorem typing_var0_prop : Typing [.srt .prop] (.var 0) (.srt .prop) := by
  simpa [lift] using Typing.var (i := 0) (A := .srt .prop) wf_prop rfl

/-- `A : Prop, x : A` is well formed. -/
theorem wf_prop_var : Wf [.var 0, .srt .prop] := Wf.cons wf_prop typing_var0_prop

/-- `A : Prop, x : A ⊢ A : Prop` (the variable `1`). -/
theorem typing_var1_prop : Typing [.var 0, .srt .prop] (.var 1) (.srt .prop) := by
  simpa [lift] using Typing.var (i := 1) (A := .srt .prop) wf_prop_var rfl

/-- `A : Prop, x : A ⊢ x : A` (the variable `0`, whose type is `var 1`). -/
theorem typing_var0_var1 : Typing [.var 0, .srt .prop] (.var 0) (.var 1) := by
  simpa [lift] using Typing.var (i := 0) (A := .var 0) wf_prop_var rfl

/-- `A : Prop ⊢ Π (x : A). A : Prop`. -/
theorem typing_pi_var : Typing [.srt .prop] (.pi (.var 0) (.var 1)) (.srt .prop) :=
  Typing.pi typing_var0_prop typing_var1_prop (Rl.prop _)

/-- `⊢ Π (A : Prop). Π (x : A). A : Prop` (impredicativity). -/
theorem typing_polyId_ty :
    Typing [] (.pi (.srt .prop) (.pi (.var 0) (.var 1))) (.srt .prop) :=
  Typing.pi typing_prop_nil typing_pi_var (Rl.prop _)

/-- `A : Prop ⊢ λ (x : A). x : Π (x : A). A`. -/
theorem typing_id_var : Typing [.srt .prop] (.lam (.var 0) (.var 0)) (.pi (.var 0) (.var 1)) :=
  Typing.lam typing_pi_var typing_var0_var1

theorem typing_polyId :
    Typing [] (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
      (.pi (.srt .prop) (.pi (.var 0) (.var 1))) :=
  Typing.lam typing_polyId_ty typing_id_var

/-- `⊢ Π (P : Prop). P : Prop`. -/
theorem typing_false : Typing [] (.pi (.srt .prop) (.var 0)) (.srt .prop) :=
  Typing.pi typing_prop_nil typing_var0_prop (Rl.prop _)

theorem typing_polyId_app :
    Typing []
      (.app
        (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
        (.pi (.srt .prop) (.var 0)))
      (.pi (.pi (.srt .prop) (.var 0)) (.pi (.srt .prop) (.var 0))) :=
  Typing.app typing_polyId typing_false

theorem step_polyId_app :
    Step
      (.app
        (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
        (.pi (.srt .prop) (.var 0)))
      (.lam (.pi (.srt .prop) (.var 0)) (.var 0)) :=
  Step.beta _ _ _

end Submission.Guards
