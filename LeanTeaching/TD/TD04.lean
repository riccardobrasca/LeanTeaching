import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Pi
import LeanTeaching.TutoLib

/-

Dans cette séance, nous allons apprendre à manipuler la notion
de limite de suite de nombres réels.

Le point de vue de mathlib sur cette question est bien plus général
que celui que vous apprenez en licence, il est fondé sur la notion
de filtre en topologie générale. Cette notion permet d'unifier toutes
les notions de limites qui interviennent en analyse et en géométrie,
limites de suites, de fonctions, limites à droite ou à gauche,
limites infinies, etc.

Malgré l'intérêt de ce point de vue, nous allons l'éviter ici et
redéfinir à partir du début la notion de limite qui vous est enseignée
en licence.

Une suite u est une fonction de ℕ dans ℝ, c'est-à-dire, pour Lean,
u : ℕ → ℝ

Voici la définition de limite. Si u : ℕ → ℝ est une suite de nombres réels
et l : ℝ un nombre réel de « u tend vers l » :

-- Définition de « u tend vers l »
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

Notez que l'on a simplement écrit `∀ ε > 0, ...`,
comme abréviation de l'expression
`∀ ε, ε > 0 → ... `

En particulier, si `h : seq_lim u l`, si `ε : ℝ` est un nombre réel et si `hε : ε > 0` est un terme du type `ε > 0`, alors `h ε hε` est un terme de type `∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Dans le contexte

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |u n - l| < ε

On peut aussi « appliquer δ δ_pos » à `h` via la tactique
  `specialize h δ δ_pos`
et le contexte devient
h : ∃ (N : ℕ), ∀ n ≥ N, |u n - l| < δ

Mais on peut vouloir appliquer h avec (δ/2) ;
car on a l'inégalité δ/2 > 0,
Lean/mathlib sait le démontrer automatiquement, grâce à sa tactique `linarith`.

Lorsqu'on entre
  `specialize h (δ/2) (by linarith)`
le contexte devient
h : ∃ (N : ℕ), ∀ n ≥ N, |u n - l| < δ/2

Cette même tactique sait démontrer des inégalités larges à partir
d'inégalités strictes.

We'll take this opportunity to use two new tactics:

`norm_num` will perform numerical normalization on the goal and `norm_num at h`
will do the same in assumption `h`. This will get rid of trivial calculations on numbers,
like replacing |l - l| by zero in the next exercise.

`congr'` will try to prove equalities between applications of functions by recursively
proving the arguments are the same.
For instance, if the goal is `f x + g y = f z + g t` then congr will replace it by
two goals: `x = z` and `y = t`.
You can limit the recursion depth by specifying a natural number after `congr'`.
For instance, in the above example, `congr' 1` will give new goals
`f x = f z` and `g y = g t`, which only inspect arguments of the addition and not deeper.
-/

/- Quelques lemmes sur les inégalités et valeurs absolues que vous pourrez utiliser

le_trans {a b c : ℝ} : a ≤ b → b ≤ c → a ≤ c

le_of_lt {a b : ℝ} : a < b → a ≤ b

gt_iff_lt {a b : ℝ} : a > b ↔ b < a

abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub_comm (x y : ℝ) : |x - y| = |y - x|

-/

-- Nous fixons des suites `u`, `v`, `w` et des nombres réels `l`, `l'`
variable (u v w : ℕ → ℝ) (l l' : ℝ)

-- Si u est constante de valeur l, alors u tend vers l
example : (∀ n, u n = l) → seq_limit u l := by
-- Nous devons démontrer un énoncé de type P → Q
-- On introduit la condition P avec la tactique `intro`
  intro hu
-- On développe la définition de `seq_lim`
  dsimp only [seq_limit]
-- C'est de nouveau un énoncé de type ∀ ε, ε >0, … : on introduit les deux conditions
  intros ε hε
-- Pour plus tard, on récrit l'inégalité `ε > 0` en `0 ≤ ε`
  simp only [gt_iff_lt] at hε

-- C'est un énoncé de type ∃ N, …
-- Il faut donc proposer une valeur de N à partir de laquelle la condition qui suit sera vérifiée
-- Dans le cas présent, N = 0 convient
  use 0
-- Il faut maintenant prouver que N = 0 convient
  intro n _
-- Il s'agit de montrer que |u n - l| ≤ ε :
-- on remplace u n par sa valeur telle que donnée par hu
  rw [hu]
-- La tactique norm_num est également capable de faire quelques simplifications algébriques
  norm_num
  linarith
  done


-- Supposons l > 0.
-- Si u tend vers l, alors u n ≥ l/2 pour tout n assez grand
example (hl : l > 0) : seq_limit u l → ∃ N, ∀ n ≥ N, u n ≥ l/2 := by
  sorry
  done

/-
When dealing with max, you can use

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

You should probably add them to the sheet of paper where you wrote
the `abs` lemmas since they are used in many exercises.

Let's see an example.
-/

-- If u tends to l and v tends l' then u+v tends to l+l'
example (hu : seq_limit u l) (hv : seq_limit v l') :
seq_limit (u + v) (l + l') := by
  intro ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intro n hn
  rcases ge_max_iff.mp hn with ⟨hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := by
    exact hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := by
    exact hN₂ n (by linarith)
  calc |(u + v) n - (l + l')| = |u n + v n - (l + l')| := by rfl
  _ = |(u n - l) + (v n - l')| := by congr 1; ring
  _ ≤ |u n - l| + |v n - l'|   := by apply abs_add
  _ ≤  ε                       := by linarith

/-
In the above proof, we used `have` to prepare facts for `linarith` consumption in the last line.
Since we have direct proof terms for them, we can feed them directly to `linarith` as in the next proof
of the same statement.
Another variation we introduce is rewriting using `ge_max_iff` and letting `linarith` handle the
conjunction, instead of creating two new assumptions.
-/

example (hu : seq_limit u l) (hv : seq_limit v l') : seq_limit (u + v) (l + l') := by
  intro ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intro n hn
  rw [ge_max_iff] at hn
  calc |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := by rfl
  _ = |(u n - l) + (v n - l')| := by congr 1 ; ring
  _ ≤ |u n - l| + |v n - l'|   := by apply abs_add
  _ ≤  ε                       := by linarith [hN₁ n (by linarith), hN₂ n (by linarith)]

/- Let's do something similar: the squeezing theorem. -/
example (hu : seq_limit u l) (hw : seq_limit w l)
(h : ∀ n, u n ≤ v n)
(h' : ∀ n, v n ≤ w n) : seq_limit v l := by
  sorry

/- What about < ε? -/
example (u l) : seq_limit u l ↔
 ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε := by
  sorry

/- In the next exercise, we'll use

eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y
-/

-- A sequence admits at most one limit
example : seq_limit u l → seq_limit u l' → l = l' := by
  sorry

/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by
  sorry
