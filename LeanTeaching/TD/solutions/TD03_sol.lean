import Mathlib.Tactic
import Mathlib.Data.Nat.Parity

/-

# TD 3 : Propositions

Rappelons qu'en Lean chaque « chose » a son propre type, par exemple `0` est de type `ℕ`.

Les énoncés mathématiques (vrais ou faux) ont type `Prop` (abréviation de « proposition »).

-/

-- Un énoncé vrai
#check ∀ (n : ℕ), n + 0 = n

-- Un enoncé faux (remarquez que Lean considère que `∀ n` signifie `∀ (n : ℕ)`)
#check ∀ n, n > 10

-- Le dernier théorème de Fermat
#check ∀ (x y z n : ℕ), n ≥ 3 ∧ x ^ n + y ^ n = z ^ n → x * y * z = 0

/-
`Prop` est donc « l'ensemble » (« ensemble » est utilisé ici informellement) des énoncés mathématiques.
En tant que mathématiciens on est intéressés à chercher des démonstrations. Une démonstration doit
elle même avoir son propre type! Par convention, le type d'un démonstration est l'énoncé dont elle
est une démonstration. Ça peut paraître très bizarre, mais c'est en réalité assez simple : si `P`
est un énoncé, la notation `(h : P)` signifie que `h` est de type `P`, donc que `h` est une
démonstration de `P`, donc en pratique que `P` est vrai.
-/

lemma add_one_odd_of_even (n : ℕ) (h : Even n) : Odd (n + 1) := by
  apply Even.add_odd
  · exact h
  · exact odd_one
  done

#check add_one_odd_of_even

/-
Il faut penser à `add_one_odd_of_even` comme la démonstration de l'énoncé :
  « si `n` est un entier naturel et si `n` est pair alors `n + 1` est impair. »
Remarquez que `add_one_odd_of_even` est la
*démonstration*, non pas l'énoncé lui même. Il s'agit d'un objet plus intéressant, il nous dit que
l'énoncé en question est vrai.

Remarquez aussi que `(h : Even n)` signifie littéralement que `h` est un démonstration du fait que
`n` est pair, mais on suppose cette démonstration déjà donnée, donc en pratique on suppose seulement
que `n` est pair.

Finalement, remarquez que pour l'instant Lean ne sait rien autour de « vrai » et « faux », il y a juste
des énoncés avec une démonstration (qui nous allons interpréter comme des énoncés vrais).

Si `(P Q : Prop)` sont des énoncés, on peut fabriquer des nouveau énoncés comme d'habitude
-/

variable (P Q : Prop)

-- L'énoncé « `P` et `Q` »
#check P ∧ Q

-- L'énoncé « `P` ou `Q` »
#check P ∨ Q

-- L'énoncé « »`P` implique `Q` »
#check P → Q

-- L'énoncé « `P` si et seulement si `Q` »
#check P ↔ Q

-- L'énoncé « non `P` »
#check ¬P

/-
Regardons de plus près l'énoncé `P → Q`, « `P` implique `Q` ». Cela signifie (informellement) que si
`P` est vrai alors `Q` est vrai. On a dit que « `P` est vrai » s'écrivait en Lean en disant « il y a une
démonstration de `P` », ou plus précisément en supposant que `(h : P)` est de type `P`, c'est-à-dire que « `h` est
une démonstration de `P` ». Démontrer
`P → Q` veut dire construire un terme `f` de type `P → Q`: cette notation est la même que pour
construire une fonction `f : P → Q` de `P` vers `Q` (en oubliant qu'il s'agit ici d'énoncés). Une
telle fonction prend un `h` de type `P` et doit renvoyer quelque chose de type `Q`, noté `f h`. Donc
elle prend une démonstration que `P` est vrai et renvoie une démonstration de `Q`, donc elle est une démonstration de l'énoncé « si `P` alors `Q` ».

On voit donc que utiliser la même notation pour une fonction ou une implication est très pratique
si on pense que un énoncé est « l'ensemble de ses démonstrations ». Il y a en réalité une théorie
très intéressante derrière ce que peut paraître juste une notation pratique (même si un peu
bizarre) que malheureusement on n'a pas le temps d'aborder (pour les curieux⬝ses, il s'agit de la *correspondance de Curry-Howard*, voir https://fr.wikipedia.org/wiki/Correspondance_de_Curry-Howard).
-/

example (p : P) : P := by
  exact p
  done

example : P → P := by
  intro p
  exact p
  done

example : P → P := by
  exact id
  done

example (p : P) (h : P → Q) : Q := by
  exact h p
  done

example (p : P) (h : P → Q) : Q := by
  apply h
  exact p
  done

example (R S T U: Prop) (p : P) (h : P → Q) (i : Q → R) (j : Q → T) (k : S → T) (l : T → U) : U := by
  apply l
  apply j
  apply h
  exact p
  done

example (R S T U: Prop) (p : P) (h : P → Q) (i : Q → R) (j : Q → T) (k : S → T) (l : T → U) : U := by
  exact l (j (h p))
  done

example (R S T U: Prop) (p : P) (h : P → Q) (i : Q → R) (j : Q → T) (k : S → T) (l : T → U) : U := by
  -- have : P → U := l ∘ j ∘ h
  exact (l ∘ j ∘ h) p
  done


example : P → (Q → P) := by
  intro p
  intro _
  exact p
  done

variable (R : Prop)

example : (P → Q) → (Q → R) → (P → R) := by
  intro h
  intro g
  intro p
  apply g
  apply h
  exact p
  done

example : (P → Q) → (Q → R) → (P → R) := by
  intro h
  intro g
  intro p
  exact g (h p)
  done

example : (P → Q) → (Q → R) → (P → R) := by
  intro h
  intro g
  exact g ∘ h
  done

/-
Lean connaît au moins deux énoncé, `True` et `False`.
-/

#check True

#check False

/-
On ne va pas rentrer dans leur définition, mais démontrer `true` est facile, il n'y a
essentiellement rien à faire, et la tactique `trivial` suffit.
-/

example : True := by
  trivial
  done

/-
`False` est utilisé pour exprimer qu'on a fait des hypothèses contradictoires, donc si démontre
`False` il n'y a rien de particulier, ça signifie simplement que nos hypothèses ne sont jamais toutes
vérifiées.

`False` est aussi utilisé pour *définir* la négation d'un énoncé : l'énoncé `¬P` est *par définition*
l'implication `P → False`. Concrètement, cela signifie que à chaque fois qu'on doit démontrer la
négation d'un énoncé `P` on peut commencer avec `intro h` que va supposer `P` et démontrer `False`
(donc en déduire que `P` ne peut pas être vrai).
-/

example : ¬(1 < 0) := by
  intro h -- `h` est l'hypothèse que `1 < 0`
  linarith
  done

/-
De l'autre coté, supposer `¬P` signifie supposer que `P → False`, et on peut donc appliquer cette
hypothèse.
-/

example : (P → Q) → (¬ Q → ¬ P) := by
  intro h
  intro hnq
  intro p
  apply hnq
  apply h
  exact p
  done

example (A B C D E F G H I J K L : Prop) (f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A)
  (f5 : E → F) (f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J) (f11 : J → I)
  (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L) : A → L := by
  sorry
  done

/-
Dans la feuille précédente on a démontré `¬(∃ (n : ℕ), (n + 1).Prime ∧ (n + 1) ∣ n! )` en utilisant
`by_contra`. Voyez-vous comment éviter cette tactique ?
-/

/-
Si on a une hypothèse `h : P ∧ Q`, on peut utiliser `rcases h with (hp | hq)` pour obtenir les hypothèses
`hp : P` et `hq : Q`. On peut aussi écrire `h.1`, qui est une preuve de `P`. Pour démontrer `P ∧ Q`
la tactique `constructor` produit les deux objectifs. En général `constructor` sépare en deux n'importe quel
objectif formé de deux parties (comme une double implication).
-/

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  exact hP
  exact hQ
  done

example (h : P ∧ Q) : Q ∧ P := by
  constructor
  exact h.2
  exact h.1
  done

example (h : P ∧ Q) : Q ∧ P := by
  rcases h with ⟨hp, hq⟩
  constructor
  exact hq
  exact hp
  done

example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hPQ
  intro hQR
  constructor
  exact hPQ.1
  exact hQR.2
  done


example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPQ hQR
  rcases hPQ with ⟨hPQ, hPQ'⟩
  rcases hQR with ⟨hQR, hQR'⟩
  constructor
  · intro p
    apply hQR
    apply hPQ
    exact p
  · intro r
    apply hPQ'
    apply hQR'
    exact r
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPQ hQR
  constructor
  · intro p
    apply hQR.1
    apply hPQ.1
    exact p
  · intro r
    apply hPQ.2
    apply hQR.2
    exact r
  done

/-
Si on a une hypothèse `h : P ∨ Q`, on peut utiliser `rcases h with (hp | hq)` pour obtenir deux objectifs,
dans le premier on aura `hp : P` et dans le deuxième `hq : Q`. Pour démontrer `P ∨ Q` il faut
démontrer `P` ou `Q`: la tactique `left` transforme l'objectif en `P`, la tactique `right` en `Q`.
-/

example : Q → (P ∨ Q) := by
  intro q
  right
  exact q
  done

example : Q ∨ P ↔ P ∨ Q := by
  constructor
  · intro h
    rcases h with (hq | hp)
    · right
      exact hq
    · left
      exact hp
  · intro h
    sorry
  done


example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro h
    rcases h with ⟨hp, hqr⟩
    rcases hqr with (hq | hr)
    · left
      constructor
      · exact hp
      · exact hq
    · right
      constructor
      · exact hp
      · exact hr
    done
  · intro h
    rcases h with (hpq | hpr)
    · rcases hpq with ⟨hp, hq⟩
      constructor
      · -- exact hp
        assumption
      · left
        exact hq -- assumption
    · rcases hpr with ⟨hp, hr⟩
      constructor
      · exact hp
      · right
        exact hr
  done

/-
La tactique `exfalso` transforme n'importe quel objectif en `False`. Voyez-vous l’intérêt ?
-/

example (h : P ∧ ¬P) : Q := by
  exfalso
  rcases h with ⟨hp, hnp⟩
  apply hnp
  exact hp
  done

example (h : P ∧ ¬P) : Q := by
  exfalso
  apply h.right
  exact h.left
  done

example (h : P ∧ ¬P) : Q := by
  exfalso
  exact h.right h.left
  done

/-
C'est amusant d'essayer l'exemple suivant, en utilisant seulement les tactiques `intro`, `apply`
`have`, `exfalso` et `exact`.

Après, essayez la tactique `by_contra`.
-/

example : ¬¬P → P := by
  intro h
  by_contra h'
  apply h
  assumption
  done


/-
On peut aussi utiliser la tactique `by_cases`. En effet, `by_cases h : P` produit deux objectifs,
pour le premier vous disposez de l'hypothèse `h : P`, pour le deuxième de l’hypothèse `h : ¬P`.
-/

example : P ∨ ¬ P := by
  by_cases h : P
  · left
    exact h
  · right
    exact h
  done

example : ¬ P ∨ P := by
  sorry
  done

example : (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  · intro hPQ
    intro hnQ
    intro hP
    apply hnQ
    apply hPQ
    exact hP
  · intro h
    intro p
    by_cases hq : Q
    exact hq
    exfalso
    apply h
    exact hq
    exact p
  done

example : (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  · intro hPQ
    intro hnQ
    intro hP
    apply hnQ
    apply hPQ
    exact hP
  · intro h
    intro p
    by_contra h'
    apply h
    · intro q
      apply h'
      exact q
    · exact p
  done
