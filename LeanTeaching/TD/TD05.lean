import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/- #Introduction

Le langage des ensembles, des relations, des fonctions est aujourd'hui au cœur de toutes les branches des mathématiques. Comme les fonctions et les relations peuvent être décrites comme à l'aide d'ensembles (via le graphe d'une fonction, ou d'une relation), une théorie *axiomatique* des ensembles peut servir de fondation aux mathématiques, et c'est d'ailleurs la théorie proposée par Cantor, Zermelo, Fraenkel… au début du 20e siècle qui est couramment adoptée de nos jours.

Ce ne sont pas les seules fondations possibles. Lean est fondé sur la notion de *type* et son langage permet de construire de nombreux autres types, notamment des types de fonctions entre types.
Toute expression dans Lean a un type: ce sont des nombres entiers naturels, des nombres réels, des fonctions des nombres réels dans les nombres réels, des groupes, des espaces vectoriels, etc. Certaine expressions *sont* des types, ce qui signifie que leur type est `Type`. Lean et la librairie mathlib proposent des outils pour définir des nouveaux types et des outils pour définir des objets de ces types.

Conceptuellement, on peut imaginer qu'un type est une collection d'objets. Il y a quelques avantages à exiger que chaque objet ait un type donné. Par exemple, cela permet de surcharger une notation comme `+`, et permet que l'entrée soit moins verbeuse, dès lors que Lean peut déduire beaucoup d'information du type d'un objet.
Le système de typage permet aussi à Lean de détecter des erreurs lorsqu'on applique une fonction à un mauvais nombre d'arguments, ou à des arguments du mauvais type.

La librairie de Lean définit des notions ensemblistes élémentaires. Pour Lean, au contraire de ce qui est possible en théorie des ensembles,
les éléments d'un ensemble sont toujours d'un type donné, comme les entiers naturels, ou les fonctions des nombres réels dans les nombres réels. D'une certaine manière, les ensembles de Lean doivent plutôt être considérés comme des sous-ensembles d'un type.

-/

/- # Ensembles

Si `α`est un type, le type `Set α`consiste
en les ensembles d'éléments de `α`. Sur ces types, on dispose des opérations ensemblistes et relations usuelles. Par exemple, si `s : Set α` et `t : Set α`, alors `s ⊆ t`dit que `s`est une partie de `t` (noter la graphie particulière), `s ∩ t`est l'intersection de `s`et `t`, `s ∪ t` est leur réunion.
La librairie définit également l'ensemble `univ` (« univers ») qui consiste en tous les éléments de type `α`, l'ensemble vide `∅`.
Si `x : α` et `s : Set α`, l'expression `x ∈ s` (de type `Prop`) dit que `x`est un membre de `s`; le nom des théorèmes de mathlib qui mentionnent cette notion d'appartenance contiennent souvent le mot `mem`. L'expression `x ∉ s` est une abréviation de `¬ x ∈ s`: `x` n'est pas membre de `s`.

Techniquement, `Set α` signifie `α → Prop`, c'est-à-dire qu'un ensemble est identifié à sa fonction indicatrice. Ainsi, si `x : α` et `s : set α`, `x ∈ s` est synomnyme de `s x`

-/

variable {α : Type*}
variable (s t u : Set α)

open Set

section

-- ## Union, intersection, inclusion…


/- Ce permier exemple démontre que si `s ⊆ t`, alors `s ∩ u ⊆ t ∩ u` -/
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  dsimp
  intros x hx
  constructor
  · apply h
    exact hx.left
  · exact hx.right
  done

/- Cette variante de la preuve montre
d'autres syntaxes possibles : ⟨…,…⟩ combine deux énoncés pour construire leur ∧ -/
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩
  done

/- La tactique rintro/rintros permet à Lean de construire directement `xs` et `xu` à partir du ∧ -/
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
  done

/- Ce qui s'est passé dans les exemples précédents porte le nom de *réduction définitionelle* : Lean parvient à donner sens aux diverses tactiques employées en développant les définitions des objects considérés. -/
/- Encore une version : on utilise la syntaxe λ x, … pour définir une fonction -/
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  exact fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩
  done

/- Une dernière version, dans laquelle on donne un nom au résultat prouvé -/
theorem foo (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
fun _ ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

/- Pourtant, si on remplace `theorem foo` par `example`, ça ne marche pas, ce qui indique que les mécanismes internes de Lean sont parfois subtils et que l'on ne peut pas toujours se reposer sur eux.  -/
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
fun _ ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

/- Distributivité de ∩ sur ∪ , première preuve
Comme `x ∈ s ∪ t` est défini comme `x ∈ s ∨ x ∈ t`, on peut utiliser la tactique `rcases` pour séparer les deux cas.
Observez que les règles de priorité de ∩ sur ∪ font que les parenthèses
du membre de droite sont inutiles : Lean ne les affiche pas -/
example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with (xt | xu)
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩
  done

/- seconde preuve, plus concise -/
example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  rintro x ⟨xs, xt | xu⟩
  · left
    exact ⟨xs, xt⟩
  · right
    exact ⟨xs, xu⟩
  done

/- En vous inspirant de l'exemple précédent,
démontrez le résultat suivant -/
example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  sorry
  done

/- La notation `\`signifie la différence ensembliste -/
example (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := mem_diff x

/- Exemple d'inclusion : on utilise `rcases` pour développer le `∧`et raisonner sur les deux cas du `∨`. -/
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intros x hx
  rcases hx with ⟨hxs, hxu⟩
  rcases hxs with ⟨hxs, hxt⟩
  constructor
  · exact hxs
  · -- x ∉ t ∪ u signifie ¬ (x ∈ t ∪ u), c'est-à-dire (x ∈ t ∪ u) → false
    dsimp
    intro hx'
    rcases hx' with (hx't | hx'u)
    · exact hxt hx't
    · exact hxu hx'u
  done


/- Une variante : la tactique `have` permet de prouver des résultats intermédiaires -/
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intros x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  · dsimp
    intro xtu -- x ∈ t ∨ x ∈ u
    rcases xtu with (xt | xu)
    · exact xnt xt
    · exact xnu xu
  done

-- La même preuve, plus concise — est-elle plus claire ?
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
-- La tactique `rintros` fabrique les diverses hypothèses
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  intro hx
  rcases hx with (xt | xu)
-- La tactique `contradiction` trouve toute seule la contradiction
  · contradiction
  · contradiction
  done

-- À vous !
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  sorry
  done

/- Commutativité de l'intersection.
On introduit la tactique `ext` pour « extensionalité » :
on prouve l'égalité `s = t`de deux ensembles `Set α` en montrant : `∀ x : α, x ∈ s ↔ x ∈ t`-/
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩
    exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩
    exact ⟨xs, xt⟩
  done

/- Version concise et illisible du résultat précédent
La syntaxe `$` ouvre une parenthèse qui se refermera automatiquement
au premier moment que Lean jugera possible : ici, à la fin de la ligne
Parfois, elle simplifie la lecture/écriture des expressions -/
example : s ∩ t = t ∩ s :=
Set.ext <| fun _ ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

/- Autre version : c'est un défi pour certains utilisateurs de Lean que d'écrire des preuves le plus consises possible.
Ici, cela utilise que l'intersection est définie en termes de `∧` et  `and.comm` exprime la commutativité de `∧`
On voit un `;`: il signifie que la tactique suivante s'applique à tous les buts.  -/
example : s ∩ t = t ∩ s := by
  ext x; simp [And.comm]

/- Une autre approche : on prouve l'égalité de deux ensembles par double inclusion -/
example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩
    exact ⟨xt, xs⟩
  · intro x ⟨xt, xs⟩
    exact ⟨xs, xt⟩
end

-- À vous !
example : s ∩ t = t ∩ s := by
  sorry
  done

-- À vous !
example : s ∩ (s ∪ t) = s := by
  sorry
  done

-- À vous !
example : s ∪ (s ∩ t) = s := by
  sorry
  done

-- À vous !
example : (s \ t) ∪ t = s ∪ t := by
  sorry
  done

-- À vous !
example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) := by
  sorry
  done

/- On définit les ensembles `evens` et `odds` des entiers pairs et impairs
Si `n : ℕ`, `even n ` est défini comme `∃ m : ℕ, n = m + m`
-/
def evens : Set ℕ := {n : ℕ | Even n}
def odds :  Set ℕ := {n : ℕ | ¬ Even n}


/- La réunion des entiers pairs et des entiers impairs est l'univers `Univ : Set ℕ`
Essayez de comprendre ce qui se passe dans cette preuve.
En particulier, vérifiez que vous pouvez effacer le `rw [evens, odds]`-/
example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp
  exact em _
  done

/- Observez la syntaxe pour définir un ensemble par compréhension dans l'exemple précédent :
si `s : α → Prop` est une fonction (un *prédicat*),
`{ x : α| s x }` est une autre notation pour cet ensemble. On peut aussi écrire `{x | s x }` car Lean déduit tout seul que le type de `x` doit être `α`.
D'ailleurs, les opérations sur les ensembles sont définies à l'aide de cette syntaxe :
- `s ∩ t` comme `{x | x ∈ s ∧ x ∈ t}`,
- `s ∪ t` comme `{x | x ∈ s ∨ x ∈ t}`,
- `∅` comme `{x | false}`, et
- `univ` comme `{x | true}`.

-/


/- Par définition, aucun élément n'appartient à l'ensemble vide : -/
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False := by
  exact h
  done

-- La même chose, plus direct
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

-- Tout entier appartient à l'univers
example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

-- À vous !
/- Vous pourrez utiliser les deux théorèmes `Nat.Prime.eq_two_or_odd` et `Nat.even_iff`. -/
example : { n | Nat.Prime n } ∩ { n | n > 2} ⊆ { n | ¬ Even n } := by
  intro n
  sorry
  done

#check Nat.Prime.eq_two_or_odd
#check Nat.even_iff

/- Une subtilité de la librairie mathlib (et aussi une force…) est qu'elle dispose de plusieurs prédicats `Prime`. Le plus général fait sens dans tout monoïde commutatif ayant un élément absorbant, tandis que le prédicat `Nat.Prime` ne s'applique qu'aux entiers.
Bien sûr, ils coïncident dans ce cas -/

#print Prime
#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n := Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h
  done

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]
  done
-- La tactique `rwa` combine `rw` et `assumption`

section
/- ## Quantificateurs ensemblistes (“bounded quantifiers”)
Lean propose une notation `∀ x ∈ s, …` pour dire « pour tout `x` dans `s`, …” ; c'est une abréviation de `∀ x, x ∈ s → …''.
De même, il existe une notation `∃ x ∈ s,… ` pour dire « il existe `x` dans `s`tel que … » , et c'est une abréviation de `∃ x, x ∈ s ∧…` (théorème `bex_def`).
Ces quantificateurs s'appellent “bounded quantifiers” en anglais, et les noms des théorèmes qui les utilisent contiennent souvent `ball` (“bounded for all”) ou `bex` (“bounded exists“).
Les tactiques `intros`, `use`… se comportent souvent bien, si bien qu'il n'est en général pas nécessaire d'utiliser `bex_def`.
-/

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬ Even x) (h₁ : ∀ x ∈ s, Prime x) :
  ∀ x ∈ s, ¬ Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  · apply h₁ x xs
  done

example (h : ∃ x ∈ s, ¬ Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x

section
variable (ssubt : s ⊆ t)

/- Les commandes `variable` et `variables` définissent des noms de variables ; Lean comprend tout seul qu'il faut les utiliser dès qu'elles apparaissent dans l'énoncé.. -/

-- À vous
example (h₀ : ∀ x ∈ t, ¬ Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬ Even x ∧ Prime x := by
  sorry
  done

example (h : ∃ x ∈ s, ¬ Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  sorry
  done

/- Ce bloc `section … end` délimite la portée du `include` introduit plus haut -/
end

/- Et celui-ci délimite la portée de l'introduction de la variable `ssubt`. -/
end

/- ## Unions et intersections indexées
De même qu'on représente une suite (u_0,u_1,...) de nombres réels comme une fonction ℕ → ℝ, une famille d'ensembles (d'éléments d'un type α) indexée par un type I est une fonction `A : I → set α`.
Alors `⋃ i, A i` représente leur union, et `⋂ i, A i` leur intersection.
-/
section
variable {α I : Type*} (A B : I → Set α) (s : Set α)

/- Les parenthèses servent à délimiter la portée des opérateurs -/
example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  · rintro ⟨i, xAi, xs⟩
    exact ⟨xs, ⟨i, xAi⟩⟩
  done

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    · intro i
      exact (h i).2
  · intro ⟨h1, h2⟩ i
    constructor
    · exact h1 i
    · exact h2 i
  done

open Classical

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) := by
  ext x
  simp only [mem_union, mem_iInter]
  sorry
  done

def primes : Set ℕ := {x | Nat.Prime x}

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} := by
  ext
  simp only [mem_iUnion, mem_setOf_eq, exists_prop]
  done

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} := by
  ext
  simp
  done

example : (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x = 1} := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd
  done

/- Dans l'exemple suivant, uilisez que le théorème `Nat.exists_infinite_primes` que l'ensemble des nombres premiers est infini -/
#check Nat.exists_infinite_primes

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ := by
  sorry
  done

end

section
/- ## Unions et intersections d'ensembles d'ensembles
Lean a construit le type `set α`, dont les membres sont des ensembles dont les éléments sont de type `α` ; on peut poursuivre la construction, les membres `s` du type `set (set α)` sont des ensembles d'ensembles…  On peut prendre leur union `⋃₀ s` et leur intersection `⋂₀ s`, respectivement définis comme
  - `⋃₀ s = { x | ∃ t ∈ s, x ∈ t }`
  - `⋂₀ s = { x | ∀ t ∈ s, x ∈ t }`
  -/

variable {α : Type*} (s : Set (Set α))

/- Les deux exemples suivants s'appellent `sUnion_eq_bUnion` and `sInter_eq_biInter` dans mathlib.
-/
example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  simp only [mem_sUnion, mem_iUnion, exists_prop]
  done

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  simp only [mem_sInter, mem_iInter]
  done

end
