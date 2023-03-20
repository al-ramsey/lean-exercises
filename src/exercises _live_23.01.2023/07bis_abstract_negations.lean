import data.real.basic

open_locale classical

/-
Theoretical negations.

This file is for people interested in logic who want to fully understand
negations.

Here we don't use `contrapose` or `push_neg`. The goal is to prove lemmas
that are used by those tactics. Of course we can use
`exfalso`, `by_contradiction` and `by_cases`.

If this doesn't sound like fun then skip ahead to the next file.
-/

section negation_prop

variables P Q : Prop

-- 0055
example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,
  intros a b,
  by_contradiction H,
  apply b,
  apply a,
  exact H,
  intros a b,
  by_contradiction H,
  apply a,
  exact H,
  exact b,
end

-- 0056
lemma non_imp (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q :=
begin
  split,
  intro h,
  by_contradiction H,
  apply h,
  intro p,
  by_contradiction HH,
  apply H,
  exact ⟨p, HH⟩,
  intros h a,
  apply h.right,
  apply a,
  exact h.left,
end

-- In the next one, let's use the axiom
-- propext {P Q : Prop} : (P ↔ Q) → P = Q

-- 0057
example (P : Prop) : ¬ P ↔ P = false :=
begin
  split,
  intro h,
  apply propext,
  split,
  apply h,
  intro f,
  exfalso,
  apply f,
  intro h,
  by_contradiction H,
  rw ← h,
  exact H,
end

end negation_prop

section negation_quantifiers
variables (X : Type) (P : X → Prop)

-- 0058
example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  split,
  intro h,
  by_contradiction H,
  apply h,
  intro x,
  by_contradiction HH,
  apply H,
  use x,
  intro h,
  by_contradiction H,
  cases h with x hx,
  specialize H x,
  apply hx,
  exact H,
end

-- 0059
example : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x :=
begin
  split,
  intros h x hx,
  apply h,
  use x,
  exact hx,
  intros h hx,
  cases hx with x hhx,
  specialize h x,
  apply h,
  exact hhx,
end

-- 0060
example (P : ℝ → Prop) : ¬ (∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬ P ε :=
begin
  split,
  intros h ε ε_pos hε,
  apply h,
  use ε,
  exact ⟨ε_pos, hε⟩,
  intros h hx,
  cases hx with ε hh,
  cases hh with ε_pos hε,
  specialize h ε ε_pos,
  apply h,
  exact hε,
end

-- 0061
example (P : ℝ → Prop) : ¬ (∀ x > 0, P x) ↔ ∃ x > 0, ¬ P x :=
begin
  split,
  intro h,
  by_contradiction H,
  apply h,
  intros x x_pos,
  by_contradiction HH,
  apply H,
  use x,
  exact ⟨x_pos, HH⟩,
  intros h hx,
  cases h with x hhx,
  cases hhx with hxx hh,
  specialize hx x hxx,
  apply hh,
  exact hx,
end

end negation_quantifiers

