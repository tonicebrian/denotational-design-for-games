# Introduciton
```agda
module plfa.Induction where
open import Data.Nat
open import Data.Nat.Properties
import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
```

Show that you can swap parenthesis for naturals

```agda
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap m n p =
      begin
        m + (n + p)
      ≡⟨ +-assoc m n p ⟩
        (m + n) + p
      ≡⟨ cong (_+ p) +-comm m n ⟩
        (n + m) + p
      ≡⟨ +-assoc n m p ⟩
        n + (m + p)
      ∎
```
