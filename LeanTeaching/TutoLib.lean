import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Parity
import Mathlib.Topology.Sequences

attribute [instance] Classical.propDecidable

/-
Lemmas from that file were hidden in my course, or restating things which
were proved without name in previous files.
-/

-- The mathlib version is unusable because it is stated in terms of ≤
lemma ge_max_iff {α : Type*} [LinearOrder α] {p q r : α} : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

/- No idea why this is not in mathlib-/
lemma eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y := by
  intro h
  apply eq_of_abs_sub_nonpos
  by_contra! H
  specialize h ( |x-y|/2) (by linarith)
  linarith

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

lemma unique_limit {u l l'} : seq_limit u l → seq_limit u l' → l = l' := by
  intros hl hl'
  apply eq_of_abs_sub_le_all
  intros ε ε_pos
  specialize hl (ε/2) (by linarith)
  cases' hl with N hN
  specialize hl' (ε/2) (by linarith)
  cases' hl' with N' hN'
  specialize hN (max N N') (le_max_left _ _)
  specialize hN' (max N N') (le_max_right _ _)
  -- calc |l - l'| ≤ ?_ := by sorry
  -- _ ≤ ε := by sorry
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| := by ring_nf
  _ ≤ |l - u (max N N')| + |u (max N N') - l'| := by apply abs_add
  _ = |u (max N N') - l| + |u (max N N') - l'| := by rw [abs_sub_comm]
  _ ≤ ε/2 + ε/2 := by linarith
  _ = ε := by ring

lemma le_of_le_add_all {x y : ℝ} :
  (∀ ε > 0, y ≤ x + ε) →  y ≤ x := by
  contrapose!
  intro h
  use (y-x)/2
  constructor <;> linarith

def upper_bound (A : Set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

def is_sup (A : Set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y

lemma lt_sup {A : Set ℝ} {x : ℝ} (hx : is_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a := by
  intro y
  contrapose!
  exact hx.right y

lemma squeeze {u v w : ℕ → ℝ} {l} (hu : seq_limit u l) (hw : seq_limit w l)
(h : ∀ n, u n ≤ v n)
(h' : ∀ n, v n ≤ w n) : seq_limit v l := by
  intros ε ε_pos
  cases' hu ε ε_pos with N hN
  cases' hw ε ε_pos with N' hN'
  use max N N'
  intros n hn
  rw [ge_max_iff] at hn
  specialize hN n (by linarith)
  specialize hN' n (by linarith)
  specialize h n
  specialize h' n
  rw [abs_le] at *
  constructor <;> linarith

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

def tendsto_infinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

lemma lim_le {x y : ℝ} {u : ℕ → ℝ} (hu : seq_limit u x)
  (ineg : ∀ n, u n ≤ y) : x ≤ y := by
  apply le_of_le_add_all
  intros ε ε_pos
  cases' hu ε ε_pos with N hN
  specialize hN N (by linarith)
  specialize ineg N
  rw [abs_le] at hN
  linarith

lemma inv_succ_le_all :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 tendsto_one_div_add_atTop_nhds_0_nat (ε/2) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  convert (lt_trans (hN n hn) (half_lt_self hε)).le using 1
  simp only [one_div, Real.dist_eq, sub_zero]
  rw [abs_of_nonneg]
  simp only [inv_nonneg]
  linarith

lemma limit_const (x : ℝ) : seq_limit (fun _ ↦ x) x :=
fun ε ε_pos ↦ ⟨0, fun _ _ ↦ by simp [le_of_lt ε_pos]⟩

lemma limit_of_sub_le_inv_succ {u : ℕ → ℝ} {x : ℝ} (h : ∀ n, |u n - x| ≤ 1/(n+1)) :
seq_limit u x := by
  intros ε ε_pos
  rcases inv_succ_le_all ε ε_pos with ⟨N, hN⟩
  use N
  intros n hn
  specialize h n
  specialize hN n hn
  linarith

lemma limit_const_add_inv_succ (x : ℝ) : seq_limit (fun n ↦ x + 1/(n+1)) x :=
limit_of_sub_le_inv_succ (fun n ↦ by rw [abs_of_pos] <;> linarith [@Nat.one_div_pos_of_nat ℝ _ n])

lemma limit_const_sub_inv_succ (x : ℝ) : seq_limit (fun n ↦ x - 1/(n+1)) x := by
  refine limit_of_sub_le_inv_succ (fun n ↦ ?_)
  rw [show x - 1 / (n + 1) - x = -(1/(n+1)) from by ring, abs_neg,  abs_of_pos]
  linarith [@Nat.one_div_pos_of_nat ℝ _ n]

lemma id_le_extraction {φ}: extraction φ → ∀ n, n ≤ φ n := by
  intros hyp n
  induction' n with n hn
  · exact Nat.zero_le _
  · exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])

lemma seq_limit_id : tendsto_infinity (fun n ↦ n) := by
  intros A
  cases' exists_nat_gt A with N hN
  use N
  intros n hn
  have : (n : ℝ) ≥ N := by exact_mod_cast hn
  linarith

variable {u : ℕ → ℝ} {l : ℝ} {φ : ℕ → ℕ}

open Set Filter

def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

lemma bolzano_weierstrass {a b : ℝ} {u : ℕ → ℝ} (h : ∀ n, u n ∈ Icc a b) :
∃ c ∈ Icc a b, cluster_point u c := by
  rcases (isCompact_Icc : IsCompact (Icc a b)).tendsto_subseq h with ⟨c, c_in, φ, hφ, lim⟩
  refine ⟨c, c_in, φ, hφ, ?_⟩
  simp_rw [Metric.tendsto_nhds, eventually_atTop, Real.dist_eq] at lim
  intros ε ε_pos
  rcases lim ε ε_pos with ⟨N, hN⟩
  use N
  intros n hn
  exact le_of_lt (hN n hn)

lemma not_seq_limit_of_tendstoinfinity {u : ℕ → ℝ} :
  tendsto_infinity u → ∀ x, ¬ seq_limit u x := by
  intros lim_infinie x lim_x
  cases' lim_x 1 (by linarith) with N hN
  cases' lim_infinie (x+2) with N' hN'
  let N₀ := max N N'
  specialize hN N₀ (le_max_left _ _)
  specialize hN' N₀ (le_max_right _ _)
  rw [abs_le] at hN
  linarith

open Real

lemma sup_segment {a b : ℝ} {A : Set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ Icc a b) :
  ∃ x ∈ Icc a b, is_sup A x := by
  have b_maj :  ∀ (y : ℝ), y ∈ A → y ≤ b := fun y y_in ↦ (h y_in).2
  have Sup_maj : upper_bound A (sSup A) := by
    intro x
    apply le_csSup
    exact ⟨b, b_maj⟩
  refine ⟨sSup A, ?_, ?_⟩
  · constructor
    · cases' hnonvide with x x_in
      exact le_trans (h x_in).1 (Sup_maj _ x_in)
    · apply csSup_le hnonvide b_maj
  · exact ⟨Sup_maj, fun y ↦ csSup_le hnonvide⟩

lemma subseq_tendsto_of_tendsto (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by
  intros ε ε_pos
  cases' h ε ε_pos with N hN
  use N
  intros n hn
  apply hN
  calc N ≤ n := hn
  _ ≤ φ n := id_le_extraction hφ n
