import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Int.Parity

open Nat

/-

# TD 2 : Nombres naturels

Comme on a vu dans le premier TD,
le langage Lean a défini le type des entiers naturels, qui est noté `ℕ` ;
il fournit aussi de nombreuses constructions (opérations arithmétiques,
par exemple), et la librairie Mathlib le complète avec une large gamme
de théorèmes.

La définition utilisée par Lean est celle de Peano.

Essentiellement, `ℕ` est défini axiomatiquement comme un *type* vérifiant
les propriétés suivantes :
* Il existe un élément `zero` de type `ℕ`, donc `(zero : ℕ)` fait du sense.
* Il y a un fonction `succ : ℕ → ℕ`.
* Le principe de récurrence est vrai (on précisera ça ci-dessous).

Dans ce TD, on va *refaire* à la main cette construction, définir
l'addition et la multiplication, et démontrer quelques propriétés de base.
Pour éviter les confusions, « notre » type d'entiers s'appellera `N`.

-/

inductive N : Type
  | zero : N
  | succ : N → N

/-
Le mot clé `inductive` dit à Lean que on est en train de définir
un *type inductif*.  Intuitivement "type" est un synonyme de
"ensemble" et "inductif" signifie qu'on va spécifier comment il est
possible de "créer" des éléments de cet ensemble.
La ligne `inductive N : Type` veut donc dire qu'on va définir un
ensemble, appelé `N`.  Les deux lignes suivantes sont plus intéressantes :
elles donnent la liste des *constructeurs* de `N`, c'est-à-dire
toutes le manières possibles pour "créer" un élément de `N`.
Il n'y en a que deux !
* ` | zero : N` dit simplement qu'il existe un élément de `N`, appelé `N.zero`,
donc Lean va accepter la syntax `(N.zero : N)`.
* `| succ : N → N` dit qu'il existe un fonction de `N` dans `N`,
(appelé automatiquement `N.succ`) qui peut donc être utilisé pour produire
des autres éléments de `N` : si `(n : N)`, `N.succ n` sera aussi un élément
de `N` (un terme de type `N` pour être précis).
Par exemple `N.succ N.zero : N`.

-/

-- `N` est un type
#check N

-- `N.zero` est un membre du type `N`
#check N.zero

-- `N.succ` est une fonction de `N` dans `N`
#check N.succ

/- (La façon donc Lean affiche ce résultat est un peu malpratique,
dans l'expression écrite, `a✝ : N` représente un élément de `N` noté `a✝`,
et l'espèce de croix veut dire que cette variable est muette.
C'est un peu comme si on notait `sin (x)` pour parler de la fonction sinus.)  -/

-- Cette ligne nous évitere de devoir taper `N.` à chaque fois.
namespace N

/- La commande `namespace N` fait en sorte que toutes les déclarations
(définitions, théorèmes...) écrites avant `end N` aient un nom qui
commence par `N.`. C'est utile pour pouvoir considérer des noms
déjà utilisés ailleurs. Par exemple `add_zero` ci-dessous en réalité
s'appelle `N.add_zero` et il n'est pas en conflit avec le `add_zero`
« standard » de Lean.  -/

-- `zero` est en fait `N.zero`
#check zero

-- `succ` est la fonction `N.succ`
#check succ

/- Remarquez que « notre » ensemble de nombres naturels s'appelle
`N`, *pas* `ℕ`. Le symbole `ℕ` est réservé pour les nombres naturels
défini en Lean. En faisant ctrl + click sur `ℕ` ci-dessous vous
pouvez vérifier que notre définition est exactement la même que
celle « officielle » (attention à ne rien toucher dans le fichier
qui s'ouvre, sinon Lean croit que vous avez changé la définition
de `ℕ` et il va vérifier que les maths sont encore cohérentes, ce
qui va prendre beaucoup de temps !!).  -/

#check ℕ

instance : Zero N := ⟨zero⟩
-- local attribute [reducible] Zero N

/-
Ces lignes rendent simplement disponible la notation `0 : N`, en
définissant `0` comme `N.zero`, vous pouvez ignorer la deuxième.

Attention : `0`, sans rien d'autre est encore réservé au `0` des
« vrais » nombres naturels.  -/

-- `(0 : N)` est le zéro de `N`
#check (0 : N)

-- Attention, `0` est le zéro de `ℕ` : à ne pas utiliser aujourd'hui
#check 0

-- Le successeur de `(0 : N)`
#check succ (0 : N)

-- Le successeur de `0`
#check succ 0

/- On voit ici une des choses que Lean sait faire automatiquement :
lorsqu'il lit `succ 0`, il comprend qu'il s'agit de `0 : N` parce
que `succ` est d'abord l'abréviation de `N.succ` qui prend en argument
un terme de type `N`. -/

-- Le successeur du successeur de `0`
#check succ (succ 0)

/-
On a donc un élément `0 : N` et une fonction `succ : N → N`.
Comment prouver des théorèmes ?

Dans la définition de Peano, l'axiome supplémentaire est le principe
de récurrence. Pour l’énoncer, il faut introduire « l'ensemble » (en réalité,
un type) `Prop` des énoncés mathématiques, qu'on étudiera en détail dans un
prochain TD.

Pour l'instant la seule chose a savoir est un terme de type `Prop`
est un énoncé mathématique (une « proposition »), qui peut être vrai ou faux.

Un premier exemple d'énoncé mathématique est
« tout entier naturel `n` est somme de quatre carrés ».
Il est juste (c'est un théorème de Lagrange) mais difficile à démontrer.
Un autre exemple d'énoncé mathématique est « tout entier naturel `n` est pair ».
Celui-là est évidemment faux, mais cela reste quand-même un énoncé.

Si `n` est un nombre naturel fixé, un autre énoncé est « `n` est pair ».
Il est vrai ou faux, cela dépend de `n`.
Cet énoncé est donc une fonction `N → Prop`.

Plus généralement, une fonction `f : N → Prop` est la
donnée d'un énoncé `f n` pour chaque `n : N`, par exemple « `n` est pair ».

Le principe de récurrence dit la chose suivante.
Soit `f : N → Prop` une fonction (donc pour chaque `n` on a l'énoncé ` f n`).
Si `f 0` est vrai et si pour tout `n` on sait que `f n` implique `f (succ n)`,
alors `f n` est vrai pour tout `n`.

En Lean, l'implication entre deux propositions `P` et `Q` s'écrit simplement
`P → Q`, voici donc le principe de récurrence.
-/

theorem induction
    (f : N → Prop)
    (hzero : f 0)
    (H : ∀ n, f n → f (succ n)) :
    ∀ n, f n :=
  N.rec hzero H

/-
La ligne `theorem induction` dit simplement qu'on va démontrer
un théorème qu'on appelle `induction`.
Après il y a les hypothèses de ce théorème :
* `(f : N → Prop)` signifie « Soit `f` une fonction de `N` vers `Prop` »,
  de sorte que pour tout `n : N`, on a un énoncé `f n`.
* `(hzero : f 0)` signifie que `hzero` est la propriété d'initialisation :
  « `f 0` est vrai ».
  Remarquez qu'il n'a pas fallu préciser que `0` est le zéro de `N` ;
  Lean l'a compris parce que `f` prend un terme de type `N`.
  Ignorez pour l'instant le fait que cette ligne semble dire
  « soit `hzero` un terme de type `f 0` » : on en parlera la semaine prochaine.
* `(H : ∀ n, f n → f (succ n))` signifie que `H` est la propriété d'hérédité
  pour `f n`.

Finalement, la ligne `∀ n, f n` est simplement le fait que `f n` est vrai
pour tout `n : N`.

La démonstration est simplement `N.rec hzero H`...
mais qu'est-ce que cette fonction `N.rec` ?
Il s'agit en fait du principe de récurrence créé automatiquement par Lean
quand on a défini `N` : il est vrai axiomatiquement et il implique la
formulation standard du principe de récurrence.

Il nous reste un dernier ingrédient à introduire pour pouvoir
démontrer des théorèmes intéressants. Le principe de récurrence
est en fait plus fort que celui énoncé ci-dessus. En effet, il permet non
seulement de démontrer des résultats, mais aussi de *définir* des
fonctions sur `N` : pensez aux suites définies par récurrence !

Imaginez vouloir définir une function `f` de `N` vers un ensemble
donné `S`. Si vous avez choisi l'image de `0 : N` et, à chaque fois que
vous connaissez l'image de `n : N`, vous avez une formule
pour déterminer l'image de `succ n`.
Alors `f` est complètement définie : c'est exactement comme cela qu'on
définit des suites par récurrence.

Par exemple, vous connaissez l'image de `succ 0`, parce que vous connaissez
l'image de `0`, et donc vous connaissez l'image de `succ (succ 0)`...
En pratique c'est le fait que dans `N`, tous les éléments sont construits
à partir de `0` et de la fonction `succ`.

Voici cette construction en Lean.
-/

def recursion
    (S : Type)
    (image_zero : S)
    (image_succ : N → S → S) :
    N → S := fun n ↦ by
  match n with
  | zero => exact image_zero
  | succ n => exact image_succ n (recursion S image_zero image_succ n)

#check N.rec

/-
Examinons cette définition.

* `def recursion` dit qu'on est en train de définire un objet appelé `recursion`.
* `(S : Type)` signifie « soit `S` un type ».
* `(image_zero : S)` signifie « soit `image_zero` un membre de `S` ».
* `(image_succ : N → S → S)` signifie « soit `image_succ` une fonction de `N` vers les fonctions de `S` vers `S` ».
  Donc, en pratique, si `n : N`, alors `image_succ n` est une fonction de `S`
  vers `S`.  C'est `image_succ` que traduit notre hypothèse « à chaque fois que
  vous connaissez l'image de `n`, vous connaissez aussi celle de `succ n` » :
  étant donné `n`, et après avoir choisi `f n`, on envoie `succ n`
  sur `image_succ n (f n)`.
* `N → S` signifie qu'on va définir une fonction de `N` vers `S`.
* Après le symbole `:= `, commence la *définition* de la fonction :
  c'est une *fonction* (`fun`) qui prend un argument `n` et associe (`↦`)
  quelque chose construit après le mot-clé `by`.
  Avec la tactique `match n with`,oOn divise la définition en deux cas,
  suivant les deux possibilités pour la valeur de `n`.
  La première ligne traite le cas où cet élément est `zero`, la valeur est
  `image_zero` ;
  la seconde celui où cet élément est de la forme `succ n`, pour `n : N`,
  et la valeur est obtenue en appliquant `image_succ n` à l'élément
  `recursion S image_zero image_succ n` supposé construit par récurrence.

En résumant, si `S` est un type, `image_zero` est un terme de type `S`
et `image_succ` est comme ci-dessus, alors `recursion S image_zero image_succ`
est une fonction `N → S`.

Vérifions-le !
-/

variable (S : Type) (image_zero : S) (image_succ : N → S → S)

-- `recursion` ?
#check recursion S image_zero image_succ

-- On introduit une abréviation pour éviter d'écrire `recursion…` à chaque fois
local notation3 "f" => recursion S image_zero image_succ

-- `f` ?
#check f

/-
On a donc défini une fonction `f : N → S`.
Pour vérifier que il s'agit bien de la construction usuelle par récurrence,
il reste à vérifier que l'image de `0` est bien `image_zero` et que l'image
de `succ n` est bien `image_succ n (f n)`.
Les deux sont vrais à cause de l'axiomatique de Lean,
et il n'y a en fait rien à démontrer !

-/

#check (0 : N)

/-- Initialisation : `f 0 = image_zero` -/
lemma f_zero : f (0 : N) = image_zero := by
  rfl -- la tactique `rfl` constate que `f 0 = image_zero`
  done

/-- Héridité : `f (succ n) = image_succ n (f n)` -/
lemma f_succ (n : N) : f (succ n) = image_succ n (f n) := by
  rfl -- la tactique `rfl` constate que `f (succ n) = image_succ n (f n)`
  done

section addition

/-
On va maintenant définir l'addition.
Depuis les travaux de Peano et Dedekind vers 1880, l'idée est la suivante :
la fonction somme est une fonction de deux variables, mais pour tout `n : N`,
on définit `n + m` par récurrence sur `m`, par les deux relations :
  `n + 0 = n` et `n + (succ m) = succ (n + m)`.
Grâce au principe de récurrence, on obtient une fonction,
appelée ci-dessous `add n` de `N` vers `N`, qui envoie `m` sur `n + m`.
En faisant varier aussi `n`, on obtient donc une fonction `add : N → N → N`.

Lean met à disposition une notation simple pour utiliser la récurrence
en évitant d'utiliser explicitement `N.rec`, la voici.  -/

/-- addition de deux entiers -/
def add (n : N) : N → N
| 0 => n
| succ m => succ (add n m)

-- La fonction `add`
#check add

instance : Add N := ⟨add⟩ -- Pour pouvoir utiliser la notation `n + m`

variable (n m : N)

-- n + m
#check n + m

/- Vue la définition de `+`, les deux résultats suivants sont vrais par simple
  constatation !  -/

lemma add_zero (n : N) : n + 0 = n := by
  rfl
  done

lemma add_succ (n m : N) : n + (succ m) = succ (n + m) := by
  rfl
  done

/- Par contre, démontrer que `0 + n = n` est plus délicat.
En effet, on ne sait pas encore que l'addition est commutative,
et `rfl` cette fois ne marche pas.  -/

example (n : N) : 0 + n = n := by
  rfl -- renvoie un message d'erreur
  done

/- L'idée est de démontrer `0 + n = n` par récurrence sur `n`,
  en utilisant le théorème `induction` prouvé ci-dessus. -/

variable (a b c : N) --On introduit trois éléments de `N` une fois pour toute.

/- Dans le lemme suivant, Lean utilise la variable `a` introduite ci-dessus.
  C'est la même chose qu'écrire `lemma zero_add (a : N) : 0 + a = a`.
  Remarquez que Lean n'utilise pas `b` ou `c`, parce que ils n'apparaissent pas
  dans l'énoncé. -/

example : ∀ (a : N), zero + a = a := by
  -- On applique le raisonnement par récurrence
  apply N.induction
  /- On a maintenant deux buts ('2 goals') qu'on va démontrer l'un après l'autre : -/
  /- 1. Le but `hzero` : initialisation
    Il faut démontrer `zero + 0 = 0`, mais `0` est la même chose que `zero`,
    ainsi, c'est juste la définition de l'addition (ou bien `add_zero`) -/
  rw [add_zero]
  rfl
  /- 2. Le but `H` : hérédité
    Là, on  introduit un entier `a` et l'hypothèse de récurrence `hrec`. -/
  intro a hrec
  -- on commence par appliquer la définition de l'addition, via `add_succ`
  rw [add_succ zero a]
  -- on applique l'hypothèse de récurrence qui va remplacer `zero + a` par `a`
  rw [hrec]
  -- il n'y a plus rien à faire
  done


/- Lean propose une syntaxe pour écrire un peu plus facilement les démonstration
  par récurrence de ce genre. -/
lemma zero_add : 0 + a = a := by
  -- On précise faire une récurrence sur `a`
  induction a with
  /- Les deux buts ne sont plus indiqués par les noms `hzero` et `H`
    qui venaient de notre fonction `N.induction` mais par la façon
    dont `N` est défini. -/
  -- Le cas `zero`
  | zero => rfl
  -- Le cas où l'entier est de la forme `succ a`.
  -- `hrec` est l'hypothèse de récurrence
  | succ a hrec =>
    rw [add_succ, hrec]

/- On peut maintenant prouver l'associativité de l'addition.
  Remarquez que `a + b + c` sans parenthèses signifie `(a + b) + c`.
-/

#check (a + b) + c
#check a + (b + c)
#check a + b + c

/-- Associativité de l'addition -/
lemma add_assoc : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
    sorry
  | succ c hrec =>
    sorry
  done

/- D'autres propriétés de l'addition.  -/

lemma succ_add : succ a + b = succ (a + b) := by
  -- Remarquez que `succ a + b` signifie `(succ a) + b`.
  sorry
  done

-- Pour prouver la commutativité de l'addition, utilisez `succ_add`
/-- Commutativité de l'addition -/
lemma add_comm : a + b = b + a := by
  sorry
  done

/- On va définir le nombre `1` comme `succ 0`,
  donc le lemme `one_eq_succ_zero` ci-dessous est vrai par définition.
  La ligne suivante active la notation `1 : N`.  -/

instance : One N := ⟨succ 0⟩

#check (1 : N)

lemma one_eq_succ_zero : (1 : N) = succ 0 := by
  rfl
  done

/- Même s'il n'est pas difficile,
  le lemme suivant n'est pas vrai par définition !  -/

lemma succ_eq_add_one : succ a = a + 1 := by
  sorry
  done

/- Pour ce lemme, on a besoin d'une utilisation un peu plus fine
  de la tactique `rw` : Lean peut appliquer l'associativité
  à plusieurs endroits de l'énoncé, et pour qu'il le fasse à celui qu'on
  veut, on va préciser les arguments de `add_assoc`. -/

lemma add_right_comm : a + b + c = a + c + b := by
  rw [add_assoc a b c] -- `rw [add_assoc]` marche aussi
  rw [add_comm b c]    -- ici on doit préciser `b` et `c`
  rw [← add_assoc]     -- `← ` dit à `rw` de récrire le lemme de droite à gauche
  done

end addition

section multiplication

/- On a défini et étudié l'addition dans `N` grâce au principe de récurrence,
  et on va faire de même pour la multiplication.
  Avant de lire la suite, essayez de donner par vous-même une définition
  de la multiplication de deux entiers, en suivant ce qu'on a fait pour
  l'addition.  -/

def mul (n : N) : N → N
| 0 => 0
| (succ m) => (mul n m) + n

instance : Mul N := ⟨mul⟩ --Active la notation `a * b`

/- Les trois variables déclarées avant ne sont plus accessibles,
  car on est dans une autre section.  -/

variable (a b c : N)

lemma mul_zero : a * 0 = 0 := by
  rfl
  done

lemma mul_succ : a * (succ b) = a * b + a := by
  rfl
  done

lemma zero_mul : 0 * a = 0 := by
  sorry
  done

lemma mul_one : a * 1 = a := by
  sorry
  done

lemma one_mul : 1 * a = a := by
  sorry
  done

lemma mul_add : a * (b + c) = a * b + a * c := by
  sorry
  done

lemma mul_assoc : a * b * c = a * (b * c) := by
  sorry
  done

lemma succ_mul : succ a * b = a * b + b := by
  sorry
  done

lemma add_mul : (a + b) * c = a * c + b * c := by
  sorry
  done

lemma mul_comm : a * b = b * a := by
  sorry
  done

end multiplication

section power

/- On définit maintenant les puissances.  -/

def pow (n : N) : N → N
| 0 => 1
| (succ m) => (pow n m) * n

instance : Pow N N := ⟨pow⟩ -- Active la notation `a ^ b`

variable (a b c : N)

lemma pow_zero : a ^ (0 : N) = 1 := by
  rfl
  done

lemma pow_succ : a ^ (succ b) = a ^ b * a := by
  rfl
  done

end power

section CommSemiring

/-   On fait observer à Lean que `N` est un « semi-anneau commutatif. »

  Le cours d'algèbre définit *anneau* comme un ensemble muni
  de deux opérations associatives `+` et `*`,
  ayant un élément neutre (`0` pour `+` et `1` pour `*`),
  avec une propriété de distributivité de la multiplication sur l'addition,
  l'addition doit aussi être commutative.
  Ces propriétés sont celles d'un *semi-anneau*, mais dans un *anneau*,
  il faut en outre que tout élément ait un opposé pour `+`.
  Un *anneau* ou un *semi-anneau* est commutatif lorsque la multiplication
  est commutative.

  Remarquez que ces propriétés ont toutes été vérifiées avant ! -/

/-- `N` est un semi-anneau commutatif (*commutative semiring*) -/
instance : CommSemiring N where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/- Une fois que Lean sait que `N` est un semi-anneau, il sait
  y interpréter tous les nombres entiers habituels -/
#check (1789 : N)

lemma two_eq_succ_one : (2 : N) = succ 1 := by
  rfl
  done

/- Un autre intérêt d'apprendre à Lean que `N` est un semi-anneau
  est qu'il sait maintenant vérifier certaines relations automatiquement
  dans `N` si elles peuvent se démontrer avec les propriétés d'un semi-anneau
  commutatif.  -/

example (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

end CommSemiring

/-
Voici un résultat pas complètement évident.
-/

example (u : N → N)
    (h0 : u 0 = 1)
    (hn : ∀ n, u (succ n) = u (n) + (2 : N) ^ n)
    (n : N) :
  u n = (2 : N) ^ n := by
  induction n with
  | zero =>
    -- Lean ne reconnaît pas `u 0`
    change u 0 = 2 ^ 0
    rw [h0]
    rfl
  | succ m hrec =>
    rw [hn m, hrec, pow_succ]
  /- On veut remplacer `2` par `1.succ`, pour utiliser `mul_succ`.
    Par contre, `2` apparaît plusieurs fois, la tactique `nth_rewrite` précise
    où effectuer la réécriture, ici à la quatrième occurrence. -/
    nth_rewrite 4 [two_eq_succ_one]
    rw [mul_succ, mul_one]
  done

end N

/- Redémontrer toutes les propriétés de `N` n'est pas raisonnable.
  Pour cette raison on abandonne ici notre version des entiers naturels,
  et on va maintenant utiliser `ℕ`, la version « officielle » de Lean.
  Ça nous donne accès à énormément de résultats déjà démontrés et nous permet
  de faire tout de suite de mathématiques non triviales.

  Voici deux exemples d'un sujet d'examen pour le cours MM1.

  Malheureusement, le symbole « ligne verticale » `|` qui sert pour la
  divisibilité est déjà réservé aux definitions inductive.
  On va donc utiliser un symbole `∣` qui peut paraître identique mais
  ne l'est pas : on l'obtient en tapant `\|` (ou `\mid`).
  Vous pouvez aussi passer la souris sur le symbole, VSCode vous dira alors
  comment l'entrer au clavier. -/

example : ∃ (n : ℕ), n ≥ 2 ∧ n ∣ (n - 1)! := by
  /- On doit montrer l'existence d'un nombre qui satisfait certaines
    propriétés. On dit à Lean de considérer `6`. -/
  use 6
  /- Il reste à vérifier que `6` marche.
    L'objectif est la conjonction (« et ») de deux parties,
    la tactique `constructor` les sépare en deux buts. -/
  constructor
  /- On a deux objectifs.
    Pour la première, une vérification directe suffit,
    grâce à la tactique `norm_num`. -/
  norm_num
  -- Pour la seconde, `norm_num` va juste simplifier l'écriture
  norm_num
  /- La définition de la divisibilité `6 ∣ 5!` est qu'il existe `k : ℕ`
    tel que `5! = 6 * k`. On propose `k = 20`. -/
  use 20
  -- Il reste à vérifier que c'est bien le cas ; Lean le constate par `rfl`.
  rfl
  done

/- Pour le deuxième exemple, on démontre qu'il n'existe pas d'entier naturel
  `n` tel que `n + 1` est premier et `n + 1` divise `n!`.
  Le symbole pour écrire la négation d'une proposition est `¬`
  et le fait que un entier `p` est premier s'écrit `p.Prime`.

  Pour cet exemple on va utiliser un résultat de Mathlib,
  le fait qu'un nombre premier `p` divise `n!` si et seulement si `p ≤ n`.
  Ce résultat est appelé `Nat.Prime.dvd_factorial`.  -/

#check Nat.Prime.dvd_factorial

/- En pratique, si `hp` est l’hypothèse que qu'un entier naturel donné est
  premier, alors `Nat.Prime.dvd_factorial hp` est la double implication
    `p ∣ n! ↔ p ≤ n`.
  On peut écrire `(Nat.Prime.dvd_factorial hp).1`
  et `(Nat.Prime.dvd_factorial hp).2` pour utiliser les deux implications.  -/

example : ¬(∃ (n : ℕ), (n + 1).Prime ∧ (n + 1) ∣ n ! ) := by
  /- Supposons que l'énoncé soit faux. On fait donc l'hypothèse, appelé `h`, qui un tel `n` existe, et on doit arriver à une contradiction,
    c'est-à-dire à démontrer `False`.
    Remarquez la tactique `by_contra` (« par contradiction »)`. -/
  by_contra h
  /- `h` est l'hypothèse qu'il existe `n` tel que une certaine propriété.
    La tactique `obtain` choisit un tel `n`.
    Ici la propriété est formée des deux parties ;
    on appelle `hprime` le fait que `n + 1` est premier
    et `hdvd` le fait que `n + 1` divise `n!`.  -/
  obtain ⟨n, hprime, hdvd⟩ := h
  /- On introduit une affirmation intermédiaire, le fait que `n + 1 ≤ n`,
    ce qui suit à cause de `Nat.Prime.dvd_factorial` et c'est une
    contradiction).
    Remarquez les tactiques `have` pour faire une affirmation intermédiaire
    et `apply` pour "appliquer" une implication. -/
  have hn : n + 1 ≤ n := by
    apply (Nat.Prime.dvd_factorial hprime).1
    exact hdvd
  /- Il y a maintenant une inégalité qui est « évidemment » fausse, mais
    bien sûr, il faut assi en faire la démonstration !
    Heureusement, la tactique `linarith` nous permet de conclure. -/
  linarith
  done

/- Voici des exemples de la feuille de TD d'arithmétique.
-/

example (n : ℕ) : Nat.gcd 13 (7 + 13 * n) = 1 := by
  have h : Nat.gcd 13 (7 + 13 * n) = Nat.gcd 13 7 := by
    exact gcd_add_mul_left_right 13 7 n
    /- Le théorème `gcd_add_mul_left_right` peut paraître impossible à trouver,
      mais remarquez la logique de son nom.
      On va voir ci-dessous des outils pour nous aider à deviner les noms des
      résultats qui existent déjà dans Mathlib. -/
  rw [h]
  norm_num -- `norm_num` suffit même sans la ligne précédente
  done

example (a b : ℤ) : 7 ∣ 10 * a + b ↔ 7 ∣ a - 2 * b := by
  constructor
  /- Pour séparer les deux buts,  on utilise une syntaxe inspirée de Python :
    chacun des deux buts est dans un bloc initié par un point centré (`·`, entré
    avec `\.`). -/
  · intro H
    /- La notation `a ∣ b` est *définie* comme `∃ c, b = a * c`. "Divise" est donc en réalité un
      énonce d'existence, et on peut utiliser `obtain` directement sur `H`. -/
    obtain ⟨k, hk⟩ := H
    /- Pour montrer une relation de divisibilité,
      qui est en réalité un énonce d'existence, on peut utiliser `use`. -/
    use -2 * k + 3 * a
    rw [mul_add, mul_comm (-2) k, ← mul_assoc, ← hk]
    /- Ici il a fallu dire à Lean comment utiliser `hk`,
      il ne suffit pas d'utiliser `ring` directement.
      On dispose de tactiques plus puissantes, par exemple `polyrith` vous
      donnerait la réponse immédiatement (en appellant la tactique
      `linear_combination`). -/
    ring
  · -- Terminez la démonstration
    sorry
  done

example (n : ℕ) : 3 ∣ (n ^ 3 + 5 * n) := by
  induction n with
  | zero => norm_num
  | succ n hrec =>
    have H : (n + 1) ^ 3 + 5 * (n + 1) = (n ^ 3 + 5 * n) + 3 * (n ^ 2 + n + 2) := by ring
    rw [H]
    /- On doit montrer que `3` divise une somme.
      Le théorème `dvd_add` dit que si un nombre divise les deux facteurs,
      alors il divise leur somme ; on peut donc l'appliquer pour obtenir deux
      objectifs. -/
    apply dvd_add
    · /- Le premier objectif est exactement notre hypthèse de récurrence. -/
      exact hrec
    · /- Le deuxième est le fait que `3` divise le produit de `3`
       	et un autre nombre, c'est qui est évident. Dans ce cas,
       	essayez la tactique `simp` (qui essaie de simplifier
       	l'objectif) est une bonne idée (ici est même suffisante).
       	Essayez d'être plus explicit avec la tactique `use`. -/
      simp
    done

example (n : ℤ) : (n + 1) ∣ n ^ 13 + 1 := by
  sorry
  done

/- D'autres exemples du cours RM1 -/

/- `Nat.odd_iff_not_even` dit qu'un nombre est impair si et seulement si
  il n'est pas pair.
  Ici, `n` est pair s'il existe `k` tel que `n = 2 * k` et il est impair
  s'il existe `k` tel que `n = 2 * k + 1`.
  Comment démontrer (sur papier !) `odd_iff_not_even` ? -/

#check odd_iff_not_even

-- `n + 1` est  pair si et seulement si `n` n'est pas pair.
#check even_add_one


lemma even_mul_add_one (n : ℕ) : Even (n * (n + 1)) := by
  /- Le théorème `even_or_odd` dit qu'un nombre est pair ou impair.
    La tactique `cases` permet de séparer les deux cas,
    en donnant un nom aux hypthèses « `n` est pair » et « `n` est impair ». -/
  cases (even_or_odd n) with
  | inl heven =>
   /- On sait que `n` est pair, et `Even.mul_right` dit que le produit
    d'un nombre pair par n'importe quel nombre entier est pair.  -/
    exact Even.mul_right heven (n + 1)
  | inr hodd =>
    have hsucc : Even (n + 1) := by
     rw [even_add_one, ← odd_iff_not_even]
     exact hodd
    exact Even.mul_left hsucc n
  done

example (n : ℤ) (h : Even (n ^ 3)) : Even n := by
  by_contra hcontra
  rw [← Int.odd_iff_not_even] at hcontra
  have H : Odd (n ^ 3)
  { -- `exact?` permet de trouver cette fonction
    exact Odd.pow hcontra }
  rw [Int.odd_iff_not_even] at H
  contradiction
  done

example (n : ℕ) : Even (n * (n + 1) * (n + 2)) := by
  /- On doit montrer que `n * (n + 1) * (n + 2)` est pair.
    Il suffit donc de montrer que `n * (n + 1)` l'est.
    La tactique `suffices H : Even (n * (n + 1))` va créer l'affirmation
      `H : Even (n * (n + 1))`
    et il vous demande de terminer votre démonstration.
    Après, il faudra bien sûr démontrer `H`.
    C'est totalement analogue à `have`, mais l'ordre des démonstrations
    à faire est inversé, et c'est parfois plus pratique.  -/
  suffices H : Even (n * (n + 1))
  exact Even.mul_right H (n + 2)
  -- On utilise le lemme `even_mul_add_one` démontré plus haut !
  exact even_mul_add_one n
  done

example (n : ℕ) : 3 ∣ n * (n + 1) * (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n hrec =>
    rw [succ_eq_add_one]
    have H : (n + 1) * (n + 2) * (n + 3) =
      n * (n + 1) * (n + 2) + 3 * (n + 1) * (n + 2) := by ring
    rw [H]
    apply dvd_add
    · exact hrec
    · rw [mul_assoc]
      -- Voyez-vous pourqui il fallait cette ligne ?
      /- `Nat.dvd_mul_right` dit qu'un nombre de la forme `a * b` est divisible
        par `a`. Elle a été trouvée par `exact?`. -/
      apply Nat.dvd_mul_right
    done
