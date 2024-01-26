import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Nat Real

/-

# TD 1 : Premiers pas en Lean

Ce texte est une suite de commandes prévues pour être exécutées par
le programme Lean, mais nous utiliserons la possibilité d'ajouter
des commentaires pour expliquer peu à peu le fonctionnement du
logiciel.

Les commentaires sont les passages écrits entre les symboles '/-'
et '-/', et également tout ce qui suit un symbole '--'.

A priori, vous lisez ce texte à l'intérieur de l'éditeur VSCode et
devriez voir à droite une colonne `Lean Infoview` qui recueille les
réponses successives du logiciel.

## Nombres et calculs

Lean permet de parler de nombreux objets mathématiques: nombres
entiers, nombres réels, fonctions, groupes, etc.,
et il est possible d'en définir de nouveaux. -/

-- voici par exemple l'entier naturel 641
#check 641

/- La commande `#check` demande à Lean de nous dire la nature d'un
objet, ici 641.  La réponse de Lean s'écrit en bleu.  On voit à
gauche du symbole `:` la *représentation* de notre entier, et à
droite son *type*, ici un entier naturel représenté par la lettre `ℕ`.
C'est un peu l'analogue de l'expression « 641 est un entier ».

De même, Lean sait parler d"entiers relatifs, de nombres rationnels,
de nombres réels ou complexes.

-/

-- Le nombre π, que Lean connaît par le nom `real.pi`.
#check Real.pi

-- Ou bien des nombres complexe `I`.
#check Complex.I

-- L'entier `-1`
#check -1

-- Le nombre rationnel `2/3` :
#check (2/3 : ℚ)

-- Le nombre rationnel `-1` :
#check (-1 : ℚ)

/- Remarquez qu'il faut spécifier à Lean que l'on parle d'entiers relatifs
  ou de nombres rationnels. -/

-- `2/3` ne renvoie pas explicitement d'erreur, mais il semble y avoir un souci
-- car vous n'auriez pas prévu que `2/3` puisse être un entier…
#check 2/3
#eval 2/3
-- Avec ces nombres, Lean est capable de faire des calculs simples,
-- grâce à la fonction #eval :
#eval 2 + 2

-- ou moins simple : là, on calcule le 5e nombre de Fermat
#eval 2 ^ (2 ^ 5) + 1

-- et vérifie qu'il est divisible par 641
-- en calculant le reste de la division euclidienne
#eval (2 ^ (2 ^ 5) + 1) % 641

/- Cela peut vous paraître anecdotique, mais Pierre de Fermat avait
  conjecturé que tous les nombres de cette forme étaient des nombres
  premiers, et il l'avait vérifié pour les 4 premiers.
  C'est Leonhard Euler qui a observé en 1732 que cela ne marchait pas
  pour le 5e. -/

/- Par contre, #eval n'est pas très utile pour les nombres réels ou complexes,
  que Lean ne sait (apparemment pas) afficher. -/

-- Essayez d'enlever les `--` de commentaires de la ligne suivante pour voir:
-- #eval (1+Complex.I) ^ 2

-- Ce calcul nous explique ce qu'est `2/3`  :
#eval 2 / 3
#eval 17 - 5
#eval (2 - 3 : ℤ)

/- Dans Lean, les fonctions de soustraction et de division ont été définies
  de sorte à « rester » du même type en étant tout le temps définies.
  Ainsi, la soustraction dans ℕ est fixée à `0` lorsqu'on devrait obtenir
  un nombre négatif, et la division est la partie entière. -/
#eval 4 - 3
#eval 5 / 2

-- En revanche, le comportement redevient celui attendu si l'on explique à Lean
-- qu'il s'agit d'entiers relatifs :
#eval (3 : ℤ) - 4
#eval (3 : ℕ) - (4 : ℤ)
-- ou de nombres rationnels :
#eval (3 : ℚ) / 5
#eval -3 / (9 : ℚ)

/- Lean a « compris tout seul » qu'il fallait convertir les entiers naturels en entiers relatifs, ou en nombres rationnels, mais il ne sait pas faire le chemin inverse -/

-- -3 + 8 vaut 5, mais c'est un entier relatif
#eval ((-3: ℤ) + 8)
#check ((-3: ℤ) + 8)

/-

## Fonctions

Lean est capable de parler de structures plus abstraites comme des fonctions.
Par exemple, on peut lui apprendre à Lean la notion de nombre de Fermat
en définissant la *fonction* qui, à un entier naturel `n` associe
le nombre de Fermat correspondant. -/

/-- Les nombres de Fermat -/
def F := fun (n : ℕ) ↦ 2 ^ (2 ^ n) + 1

/- Nous venons de *définir* une fonction `F` d'un argument `n`
  dont nous exigeons que ce soit un entier naturel.
  La définition de la fonction est l'expression écrite après le symbole `:=`,
  ici `2 ^ (2 ^ n) + 1`.

  Dans ce domaine, le mot clé `fun` est classiquement utilisé pour parler
  de fonction et écrire ce qu'on aurait noté `F : n ↦ 2 ^ (2 ^ n) + 1` en
  mathématiques.
  Cette notation est héritée du « λ-calcul«  inventé en 1931
  par le mathématicien Alonzo Church.

  Le commentaire qui précède la fonction est encadré par les caractères
  `/-- … -/` qui disent à Lean qu'il s'agit d'une documentation de la fonction.
  VSCode l'utilise pour l'afficher lorsque vous lui faites survoler
  le pointeur de votre souris.
-/

-- Qu'est-ce que `F` ?
#print F

#check F

/- On voit que c'est une fonction, comme indiqué par la flèche `→`,
  des entiers naturels (ℕ) dans eux-même. -/

-- Par contre, `F 5` est un entier naturel :
#check F 25

/- D'ailleurs, vous voyez qu'on n'a pas écrit les parenthèses,
  elles sont souvent facultatives ici, un peu comme lorsque
  vous écrivez `sin x` au lieu de `sin (x)`. -/
#check F (18)

-- Lean sait également calculer
#eval F 3
#eval F 5

/- Remarquez que savoir la nature d'un objet n'implique pas de le calculer
  explicitement.
  Par exemple, Lean peut calculer `F 18`,
  mais cela lui prend un peu de temps. -/

-- Regardez ce qui se passe lorsqu'on enlève les `--` du commentaire ci-dessous
-- #eval F 18

-- Quelles valeurs de `F` Lean parvient-il à calculer en un temps raisonnable ?

-- Par contre, comme l'indique le message d'erreur, « unknown identifier n », nous ne pouvons pas parler d'une valeur quelconque `F n`
#check F n

-- Nous pouvons ajouter à Lean le fait que pour nous, `n` représentera une variable entière.
variable (n : ℕ)

-- `n`est un entier naturel
#check n

-- et `F n ` est un entier naturel
#check F n

/-

## Théorèmes et démonstrations

De manière plus intéressante pour nous,
Lean peut aussi considérer des relations mathématiques.

Prenons par exemple la première formule de la page Wikipedia
consacrée aux nombres de Fermat : https://fr.wikipedia.org/wiki/Nombre_de_Fermat

-/

-- Une première relation
example : F (n + 1) = (F n - 1) ^ 2 + 1 := by
  dsimp only [F]
  simp only [add_tsub_cancel_right, add_left_inj]
  rw [pow_add, pow_one, pow_mul]
  done

/- Revenons maintenant mot à mot sur les lignes précédentes.
  Le mot clé `example` signifie que nous allons démontrer
  un théorème « sans nom ».
  Plus tard, nous donnerons des noms aux théorèmes que nous démontrerons :
  cela nous permettra de les réutiliser.

  Ce théorème requiert un argument, ici l'entier naturel `n : ℕ`
  et derrière le symbole `:` figure l'énoncé proprement dit,
  ici une formule algébrique qui relie les nombres de Fermat `F(n)` et `F(n+1)`.

  Puis suit le symbole `:=` qui nous avions déjà vu lors de la définition
  de la fonction `F`, puis, après `by`, une démonstration de la relation
  indiquée. Pour l'instant, ne lisez pas les trois lignes de code,
  mais placez juste le curseur au bout de la dernière ligne.
  Dans la colonne de droite `Lean Infoview`, Lean vous indique `No goals`,
  qui suggère que la démonstration est terminée.

  Un des buts de ce cours est de vous apprendre à rédiger des démonstrations
  de ce genre. -/

/- Pour commencer, revenons sur les premières commandes entrées. -/

/- Lean peut bien sûr certifier que 2 et 2 font 4 ? -/
example : 2 + 2 = 4 := by
  rfl
  done

/- example : F 15 + F 6 = F 6 + F 15 := by
  rfl
  done -/

/- Nous retrouvons la structure précédente.
  D'abord le mot clé `example`, suivi du symbole `:`,
  l'assertion `2 + 2 = 4`, le symbole `:=`, et la démonstration après `by`,
  ici formée d'une seule instruction `rfl` qui signifie :
    « Constate l'égalité. »
  De fait, Lean conclut immédiatement `No goals` !
-/

/- Pouvons-nous certifier de la même façon que `F 5` est divisible par `641` ?
  Essayons. -/

example : (F 5) % 641 = 0 := by
  rfl
  done

/-
  `rfl` est un exemple simple de ce qui s'appelle en Lean une *tactique* :
  c'est en fait un programme qui ordonne à Lean d'effectuer des calculs
  d'un certain type jusqu'à conclure, si possible, à l'égalité.

  Lean a terminé la démonstration avec `rfl`, mais Lean dispose de tactiques
  de calcul plus efficaces que l'on peut activer avec l'instruction `norm_num`.
  Notez qu'alors, il faudra dire explicitement à Lean de remplacer
  l'expression `F 5` par sa définition, c'est l'effet de la première ligne
  de la preuve ci-dessous. -/

example : (F 5) % 641 = 0 := by
  -- Remplace `F 5` par sa définition.
  dsimp only [F]
  norm_num
  done


example : F 12 + F 6 = F 6 + F 12 := by
  dsimp only [F]
  norm_num
  done


/- Lean est même capable de vérifier que des entiers sont, ou pas,
  des nombres premiers. Cette propriété est codée par le prédicat `Nat.Prime`.
  Lean sait décider si elle est vraie ou fausse en calculant la décomposition
  en facteurs premiers.  -/

-- `F 4` est un nombre premier
example : Nat.Prime (F 4) := by
  dsimp only [F]
  norm_num
  done

-- … mais pas `F 5` (le symbole `¬` signifie la négation) :
example : ¬ Nat.Prime (F 5) := by
  dsimp only [F]
  norm_num
  done

example : ¬ Nat.Prime (F 6) := by
  dsimp only [F]
  norm_num
  done

/- Pouvez-vous vérifier que les nombres de Fermat suivants ne sont pas premiers
  en remplaçant 5 par un entier un peu plus grand ?
  Probablement pas beaucoup…

  En fait, Lean n'est pas vraiment prévu pour calculer rapidement,
  il est d'abord prévu pour « calculer » rigoureusement,
  en certifiant ses calculs, et nous allons l'utiliser pour faire
  des *démonstrations mathématiques*.

-/

/-

## Récriture

Dans cette dernière partie de la séance, nous allons commencer à explorer
certaines tactiques de Lean et expliquer la démonstration donnée plus haut.

La revoici, écrite de façon moins compacte de sorte à pouvoir
étudier ligne à ligne ce qui se passe.
Prenez le temps de mettre le curseur avant chaque ligne et de regarder
ce qui se passe dans la fenêtre `Infoview` lorsque vous le déplacez à
la ligne suivante.
-/

example : F (n + 1) = (F n - 1) ^ 2 + 1  := by
  -- On voit la relation à démontrer
  dsimp [F]
  -- Tous les `F` ont été remplacés par leur expression complète
  rw [add_left_inj]
  -- `a + 1` = `b + 1` est équivalent à `a = b`
  rw [pow_add]
  -- on développe le `2 ^ (n + 1)`
  rw [pow_one]
  -- `2 ^1 = 2`
  rw [pow_mul]
  -- On applique la relation `a ^ (b * 2) = (a ^ b) ^ 2
  done

/- À part les lignes de commentaires (`-- … `)  et la seconde  (`dsimp …`),
  toutes commencent par l'instruction `rw` qui ordonne à Lean de récrire
  l'expression à l'aide de la règle donnée (`add_left_inj`, `pow_add`, etc.).  -/


-- `pow_add` est la règle qui exprime que `a ^ (m + n) = a ^ m * a ^ n :
#check pow_add

/- Ne prêtez pas trop attention au bizarre `Monoid M`,
  nous apprendrons plus tard ce qu'il signifie, et ici,
  Lean le remplacera par `ℕ` -/

#check pow_two
#check mul_add
#check mul_comm

/- Mettez le curseur au-dessus des commandes `pow_add`, `pow_two`, etc.
  que vous voyez plus haut :
  une petite fenêtre apparaît qui donne plus d'information.
  Dans Lean, la plupart des fonctions qui existent ont ce genre de
  documentation, fournie de la même façon que nous avions écrit un commentaire
  pour la fonction `F` au début. -/

/- Nous allons maintenant essayer de démontrer des relations du même genre ! -/

example : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
  rw [pow_two]
  -- on développe le carré : `(n + 1) ^ 2 = (n + 1) * (n + 1)`
  rw [mul_add]
  -- distributivité à droite
  rw [add_mul]
  -- distributivité à gauche
  rw [one_mul]
  -- `1 * a = a`
  rw [mul_one]
  -- `a * 1 = a`
  rw [← pow_two]
  -- on remet `n ^ 2 = n * n` (la flèche vers la gauche signifie
  -- qu'on applique la relation dans l'autre sens)
  rw [add_assoc, add_assoc]
  -- deux coups d'associativité
  rw [add_right_inj]
  -- simplifier les `n ^ 2`
  rw [← add_assoc]
  -- défaire l'associativité dans le membre de gauche
  rw [add_left_inj]
  -- simplifier les 1
  rw [two_mul]
  -- `2 * n = n + n`
  done

/- C'était fastidieux, d'autant plus que Lean dispose d'une tactique
  toute faite pour démontrer tout seul ce genre d'égalités : `ring` -/
example : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
  ring
  -- La tactique `ring` a convoqué automatiquement les règles de calcul valables
  done

/- ## Exercices

  Dans les `example` ci-dessous, il y a un mot-clé `sorry`
  (écrit en rouge par VSCode) qui est une tactique factice pour
  faire croire que la démonstration est complète ;
  mais cela ne le trompe pas et VSCode indique en orange
  que la déclaration utilises cette tactique.
  Il s'agit donc de remplacer ce mot-clé par des instructions Lean
  suivant les modèles déjà vus, de sorte à terminer la démonstration.

  Vous pourrez constater qu'à chaque fois, la tactique `ring` saura conclure !

  Ce qui est demandé, c'est de faire la démonstration suivant le premier modèle,
  en utilisant les fonctions qui sont apparues plus haut.

  Est-ce que les autres tactiques (`rfl`,  `norm_num`) auraient
  également fonctionné ?

  Les exercices sont classés par ordre de difficulté : ils demandent de plus
  en plus de commandes pour être résolus. -/

/- Une seule commande est nécessaire -/
example : n + n = 2 * n := by
  sorry
  done

example (m : ℕ) : m + (n + 1) = m + (n + 1) := by
  sorry
  done

example (m : ℕ) : 2 * (m + n) = 2 * m + 2 *n := by
  sorry
  done

/- Deux commandes -/
example : n + (n + 1) = 2 * n + 1 := by
  sorry
  done

example (m : ℕ) : 2 * (n + 1) = 2 * n + 2 := by
  sorry
  done

example (n : ℕ) : n * (n + 1) + 2 * (n + 1) = (n + 1) * (n + 2) := by
  sorry
  done

/- Trois commandes -/
example (m : ℕ) : (m + 1) * m = m ^ 2 + m := by
  sorry
  done

/- Quatre commandes -/

-- Vous pourrez utiliser la fonction `add_comm` qui exprime la commutativité -/
#check add_comm

example (m : ℕ) : m + (n + 1) = n + (m + 1) := by
  sorry
  done
