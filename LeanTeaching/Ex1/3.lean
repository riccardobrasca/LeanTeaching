import Mathlib.Tactic.Ring

/-  ## Exercices sur les nombres - fichier 3/4

 ### Questions

1. Expliquez les fonctions `add_assoc : ℤ → ℤ → ℤ → Prop` et `mul_comm : ℤ → ℤ → Prop`.

2. Démontrer (mathématiquement) l'exemple `N2` ci-dessous.

-/

/- ### Codage
Pour les exemples suivants, il n'est pas permis d'utiliser la tactique `ring` -/

/- Le `theorem` suivant est obligatoire.
Vous pouvez utiliser `sub_self x : x - x = 0` -/
theorem N1 (a b c d : ℤ) (hyp : c = b*a - d) (hyp' : d = a*b) : c = 0 := by
  sorry
  done

/- Choisissez *UN* entre les deux `lemma` suivants.
Vous pouvez utiliser `ring`, mais ni `dvd_add`.
On rappelle que si `a` et `b` sont des éléments de `ℤ`,
`a ∣ b` signifie que `a` divise `b`, c'est-à-dire qu'il existe `k : ℤ`
tel que `b = a * k`.

Vous pouvez utiliser les lemmes `fac_zero` et `fac_succ` ci dessous. Aussi `mul_pos`, `zero_lt_one` et
`Nat.succ_pos`, dont vous pouvez deviner l'énoncé. -/

theorem N2 (a b c : ℤ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by
  sorry
  done

def fac : ℕ → ℕ
| 0       => 1
| (n + 1) => (n + 1) * fac n

theorem fac_zero : fac 0 = 1 := rfl

theorem fac_succ (n : ℕ) : fac n.succ = n.succ * fac n := rfl

theorem N5 (n : ℕ) : 0 < fac n := by
  sorry
  done

/- Vous avez terminé le fichier 3.
*SAUVEGARDEZ IMMÉDIATEMENT VOTRE TRAVAIL SUR DISQUE DUR* et continuez avec le fichier 4.

Si vous en avez besoin, les instructions de l'examen sont à l'adresse https://github.com/riccardobrasca/LeanTeaching/blob/master/ex.md. -/
