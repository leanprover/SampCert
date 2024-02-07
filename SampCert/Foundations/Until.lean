import SampCert.Foundations.While

open Pmf

variable {T : Type} [MeasurableSpace T]

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body))  : RandomM T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) sorry v

def MyP (cond : T → Bool) (body : RandomM T) (x : T) (comp : RandomM T) : Prop :=
  comp x = (body x) / (body.toMeasure {x : T | cond x})

-- theorem prob_until_prop_aux (body : RandomM T) (cond : T → Bool) (a : T) :
--   MyP  (λ v : T => ¬ cond v) body a (prob_while (λ v : T => ¬ cond v) (λ _ : T => body) sorry a) := by
--   have H := prob_while_rule (MyP (λ v : T => ¬ cond v) body a) (λ v : T => ¬ cond v) (λ _ : T => body) sorry (Pmf.bind body (fun v => Pmf.pure v))
--   apply H
--   sorry
  -- . clear H
  --   unfold MyP
  --   simp
  --   sorry
  -- . clear H
  --   unfold MyP
  --   simp
  --   intros inner a2 H

@[simp]
theorem prob_until_apply (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body)) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) h x =
  ((body x) * (if cond x then 1 else 0)) / (body.toMeasure {x : T | cond x}) := sorry

theorem prob_until_support (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body)) :
  (prob_until (body : RandomM T) (cond : T → Bool) h).support = {x | cond x} := sorry

theorem prob_until_true (body : RandomM T) (h : terminates (fun _ => true) (λ _ => body)) :
  prob_until body (fun _ => true) h = body := by
  ext x
  rw [prob_until_apply]
  simp
