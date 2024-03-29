import tuto_lib

set_option pp.beta true
set_option pp.coercions false

/-
This is the final file in the series. Here we use everything covered
in previous files to prove a couple of famous theorems from 
elementary real analysis. Of course they all have more general versions
in mathlib.

As usual, keep in mind the following:

  abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

  ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

  le_max_left p q : p ≤ max p q

  le_max_right p q : q ≤ max p q

as well as a lemma from the previous file:

  le_of_le_add_all : (∀ ε > 0, y ≤ x + ε) →  y ≤ x

Let's start with a variation on a known exercise.
-/

-- 0071
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : seq_limit u x)
  (ineg : ∃ N, ∀ n ≥ N, y ≤ u n) : y ≤ x :=
begin
  unfold seq_limit at hu,
  cases ineg with N hN,
  by_contradiction H,
  push_neg at H,
  specialize hu ((y-x)/2) (by linarith),
  cases hu with N' hN',
  specialize hN (max N N') (le_max_left N N'),
  specialize hN' (max N N') (le_max_right N N'),
  rw abs_le at hN',
  linarith,
end

/-
Let's now return to the result proved in the `00_` file of this series, 
and prove again the sequential characterization of upper bounds (with a slighly
different proof).

For this, and other exercises below, we'll need many things that we proved in previous files,
and a couple of extras.

From the 5th file:

  limit_const (x : ℝ) : seq_limit (λ n, x) x


  squeeze (lim_u : seq_limit u l) (lim_w : seq_limit w l)
    (hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : seq_limit v l

From the 8th:

  def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

  def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y

  lt_sup (hx : is_sup A x) : ∀ y, y < x → ∃ a ∈ A, y < a :=

You can also use:

  nat.one_div_pos_of_nat {n : ℕ} : 0 < 1 / (n + 1 : ℝ)

  inv_succ_le_all :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε

and their easy consequences:

  limit_of_sub_le_inv_succ (h : ∀ n, |u n - x| ≤ 1/(n+1)) : seq_limit u x

  limit_const_add_inv_succ (x : ℝ) : seq_limit (λ n, x + 1/(n+1)) x

  limit_const_sub_inv_succ (x : ℝ) : seq_limit (λ n, x - 1/(n+1)) x

The structure of the proof is offered. It features a new tactic: 
`choose` which invokes the axiom of choice (observing the tactic state before and
after using it should be enough to understand everything). 
-/

-- 0072
lemma is_sup_iff (A : set ℝ) (x : ℝ) :
(is_sup A x) ↔ (upper_bound A x ∧ ∃ u : ℕ → ℝ, seq_limit u x ∧ ∀ n, u n ∈ A ) :=
begin
  split,
  { intro h,
    split,
    {
      exact h.left,
    },
    { have : ∀ n : ℕ, ∃ a ∈ A, x - 1/(n+1) < a,
      { intros n,
        have : 1/(n+1 : ℝ) > 0,
          exact nat.one_div_pos_of_nat,
        cases h with ha hb,
        by_contradiction H,
        push_neg at H,
        specialize hb (x - 1/(n+1)),
        have key : x ≤ x - 1/(n+1),
        apply hb,
        exact H,
        linarith,
      },
      choose u hu using this,
      use u,
      split,
      apply limit_of_sub_le_inv_succ,
      intros n,
      specialize hu n,
      rw abs_le,
      split,
      linarith,
      cases hu with ha hb,
      cases h with hx hy,
      specialize hx (u n) (ha),
      linarith,
      intros n,
      specialize hu n,
      exact hu.left,
  } },
  { rintro ⟨maj, u, limu, u_in⟩, 
    split,
    exact maj,
    intros y hy,
    by_contradiction H,
    push_neg at H,
    specialize limu ((x-y)/2) (by linarith),
    cases limu with N hN,
    specialize hN N (by linarith),
    specialize hy (u N) (u_in N),
    rw abs_le at hN,
    linarith,
  },
end

/-- Continuity of a function at a point  -/
def continuous_at_pt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

variables {f : ℝ → ℝ} {x₀ : ℝ} {u : ℕ → ℝ}

-- 0073
lemma seq_continuous_of_continuous (hf : continuous_at_pt f x₀)
  (hu : seq_limit u x₀) : seq_limit (f ∘ u) (f x₀) :=
begin
  intros ε ε_pos,
  specialize hf ε ε_pos,
  cases hf with δ ha,
  cases ha with hδ h,
  unfold seq_limit at hu,
  specialize hu δ hδ,
  cases hu with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  specialize h (u n),
  apply h,
  exact hN,
end

-- 0074
example :
  (∀ u : ℕ → ℝ, seq_limit u x₀ → seq_limit (f ∘ u) (f x₀)) →
  continuous_at_pt f x₀ :=
begin
  contrapose!,
  intro h,
  unfold continuous_at_pt at h,
  push_neg at h,
  cases h with ε hh,
  cases hh with ε_pos hε,
  have key : ∀ n : ℕ, ∃x, |x - x₀| ≤ 1/(n+1 : ℝ) ∧ ε < |f x - f x₀|,
  { intros n,
  have key₁ : 0 < (1/(n + 1 : ℝ)),
  exact nat.one_div_pos_of_nat,
  exact hε (1/(n+1)) (key₁), },
  choose u hu using key,
  use u,
  split,
  {unfold seq_limit,
  intros ε₂ ε₂_pos,
  have key₃ : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε,
  {exact inv_succ_le_all,},
  specialize key₃ ε₂ ε₂_pos,
  cases key₃ with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  specialize hu n,
  linarith, },
  unfold seq_limit,
  push_neg,
  use ε,
  split,
  exact ε_pos,
  intros N,
  use N,
  split,
  linarith,
  specialize hu N,
  linarith,
end

/-
Recall from the 6th file:


  def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

  def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
    ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a


  id_le_extraction : extraction φ → ∀ n, n ≤ φ n

and from the 8th file:

  def tendsto_infinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

  not_seq_limit_of_tendstoinfinity : tendsto_infinity u → ∀ l, ¬ seq_limit u l
-/

variables {φ : ℕ → ℕ}


-- 0075
lemma subseq_tendstoinfinity
  (h : tendsto_infinity u) (hφ : extraction φ) :
tendsto_infinity (u ∘ φ) :=
begin
  intro A,
  specialize h A,
  cases h with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n : hn 
  ... ≤ φ n : id_le_extraction hφ n,
end

-- 0076
lemma squeeze_infinity {u v : ℕ → ℝ} (hu : tendsto_infinity u)
(huv : ∀ n, u n ≤ v n) : tendsto_infinity v :=
begin
  intros A,
  specialize hu A,
  cases hu with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  calc A ≤ u n : hN
  ... ≤ v n : huv n,
end

/-
We will use segments: Icc a b := { x | a ≤ x ∧ x ≤ b }
The notation stands for Interval-closed-closed. Variations exist with
o or i instead of c, where o stands for open and i for infinity.

We will use the following version of Bolzano-Weierstrass

  bolzano_weierstrass (h : ∀ n, u n ∈ [a, b]) :
    ∃ c ∈ [a, b], cluster_point u c

as well as the obvious

  seq_limit_id : tendsto_infinity (λ n, n)
-/
open set


-- 0077
lemma bdd_above_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ M, ∀ x ∈ Icc a b, f x ≤ M :=
begin
  by_contradiction H,
  push_neg at H,
  have corr : ∀ n : ℕ, ∃ x, x ∈ Icc a b ∧ f x > n,
  {intro n,
  specialize H n,
  exact H,},
  choose u hu using corr,
  have bol : ∃ c ∈ Icc a b, cluster_point u c,
  {apply bolzano_weierstrass,
  intro n,
  specialize hu n,
  exact hu.left,},
  have inf : tendsto_infinity (f ∘ u),
  {intro A,
  apply squeeze_infinity seq_limit_id,
  intro n,
  specialize hu n,
  linarith,},
  cases bol with c hc,
  cases hc with Hc hcc,
  unfold cluster_point at hcc,
  cases hcc with φ hφ,
  specialize hf c Hc,
  have inf2 : tendsto_infinity (f ∘ (u ∘ φ)),
  { exact subseq_tendstoinfinity inf hφ.left,},
  have f_lim : seq_limit (f ∘ u ∘ φ) (f c),
  { exact seq_continuous_of_continuous hf hφ.right, },
  have cont : ¬ seq_limit (f ∘ u ∘ φ) (f c),
  { apply not_seq_limit_of_tendstoinfinity,
  exact inf2, },
  apply cont,
  exact f_lim,
end

/-
In the next exercise, we can use:

  abs_neg x : |-x| = |x|
-/

-- 0078
lemma continuous_opposite {f : ℝ → ℝ} {x₀ : ℝ} (h : continuous_at_pt f x₀) :
  continuous_at_pt (λ x, -f x) x₀ :=
begin
  unfold continuous_at_pt,
  intros ε ε_pos,
  unfold continuous_at_pt at h,
  specialize h ε ε_pos,
  cases h with δ hδ,
  cases hδ with δ_pos Hδ,
  use δ,
  split,
  exact δ_pos,
  intros x hx,
  specialize Hδ x hx,
  have key : -f x - -f x₀ = -(f x - f x₀),
  { ring,},
  rw key,
  rw abs_neg,
  exact Hδ,
end

/-
Now let's combine the two exercises above
-/

-- 0079
lemma bdd_below_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ m, ∀ x ∈ Icc a b, m ≤ f x :=
begin
  have key :  ∃ M, ∀ x ∈ Icc a b, -f x ≤ M,
  { apply bdd_above_segment,
  intros x hx,
  specialize hf x hx,
  exact continuous_opposite hf,},
  cases key with M hM,
  use -M,
  intros x hx,
  specialize hM x hx,
  linarith,
end

/-
Remember from the 5th file:

 unique_limit : seq_limit u l → seq_limit u l' → l = l'

and from the 6th one:

  subseq_tendsto_of_tendsto (h : seq_limit u l) (hφ : extraction φ) :
    seq_limit (u ∘ φ) l

We now admit the following version of the least upper bound theorem
(that cannot be proved without discussing the construction of real numbers
or admitting another strong theorem).

sup_segment {a b : ℝ} {A : set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ Icc a b) :
  ∃ x ∈ Icc a b, is_sup A x

In the next exercise, it can be useful to prove inclusions of sets of real number.
By definition, A ⊆ B means : ∀ x, x ∈ A → x ∈ B.
Hence one can start a proof of A ⊆ B by `intros x x_in`,
which brings `x : ℝ` and `x_in : x ∈ A` in the local context,
and then prove `x ∈ B`.

Note also the use of 
  {x | P x}
which denotes the set of x satisfying predicate P.

Hence `x' ∈ { x | P x} ↔ P x'`, by definition.
-/

-- 0080
example {a b : ℝ} (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ x₀ ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f x₀ :=
begin
  sorry
end

lemma stupid {a b x : ℝ} (h : x ∈ Icc a b) (h' : x ≠ b) : x < b :=
lt_of_le_of_ne h.right h'

/-
And now the final boss...
-/

def I := (Icc 0 1 : set ℝ) -- the type ascription makes sure 0 and 1 are real numbers here

-- 0081
example (f : ℝ → ℝ) (hf : ∀ x, continuous_at_pt f x) (h₀ : f 0 < 0) (h₁ : f 1 > 0) :
∃ x₀ ∈ I, f x₀ = 0 :=
begin
  let A := { x | x ∈ I ∧ f x < 0},
  have ex_x₀ : ∃ x₀ ∈ I, is_sup A x₀,
  {
    sorry
  },
  rcases ex_x₀ with ⟨x₀, x₀_in, x₀_sup⟩,
  use [x₀, x₀_in],
  have : f x₀ ≤ 0,
  {
    sorry
  },
  have x₀_1: x₀ < 1,
  {
    sorry
  },
  have : f x₀ ≥ 0,
  { have in_I : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1/(n+1) ∈ I,
    { have : ∃ N : ℕ, ∀ n≥ N, 1/(n+1 : ℝ) ≤ 1-x₀,
      {
        sorry
      },
      sorry
    },
    have not_in : ∀ n : ℕ, x₀ + 1/(n+1) ∉ A,
    -- By definition, x ∉ A means ¬ (x ∈ A).
    {
      sorry
    },
    dsimp [A] at not_in, 
    sorry
  },
  linarith,
end

