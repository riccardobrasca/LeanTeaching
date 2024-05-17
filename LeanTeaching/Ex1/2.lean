import Mathlib.Tactic.Ring

open Function

/- ## Exercices sur les fonctions - fichier 2/4 -/

/- ### Questions

On se donne des types `X`, `Y`, `Z` et des fonctions `f : X → Y`, `g : Y → Z`.

1. Donner les définitions que `f` est injective, surjective.

2. Démontrer que si `f` et `g` sont injectives, alors `g ∘ f` est injective.

3. Donner le code Lean d'un `example` qui prouverait la question précédente.
-/

/- ### Codage
Pour les exemples suivants, il n'est pas permis d'utiliser la tactique  `exact?`
(ni donc le résultat de mathlib qui démontre exactement le lemme demandé). -/

/-- Le `lemma` suivant est obligatoire. -/
theorem F1 : Surjective (fun (n : ℤ) ↦ n - 3) := by
  sorry
  done

/-- Choisissez *UN* entre les deux `lemma` suivants. -/

theorem F2 (X Y Z : Type) (f : X → Y) (g : Y → Z) (hinj : Injective (g ∘ f)) :
    Injective f := by
  sorry
  done

def even_fun (f : ℤ → ℤ) := ∀ x, f (-x) = f x

theorem F3 (f g : ℤ → ℤ) : even_fun f → even_fun g →  even_fun (f + g) := by
  sorry
  done

/- Vous avez terminé le fichier 2.
*SAUVEGARDEZ IMMÉDIATEMENT VOTRE TRAVAIL SUR DISQUE DUR* et continuez avec le fichier 3.

Si vous en avez besoin, les instructions de l'examen sont à l'adresse https://github.com/riccardobrasca/LeanTeaching/blob/master/ex.md. -/
