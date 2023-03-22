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
      ≡⟨  sym ( +-assoc m n p)  ⟩
        (m + n) + p
      ≡⟨ cong (_+ p) (+-comm m n) ⟩
        (n + m) + p
      ≡⟨ +-assoc n m p ⟩
        n + (m + p)
      ∎
```

Show multiplication distributes over addition, that is,

```agda
*-my-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-my-distrib-+ zero n p = refl
*-my-distrib-+ (suc m) n p =
   begin
     (suc m  + n) * p
   ≡⟨ cong (_* p) (+-comm (suc m) p) ⟩
      (n + suc m) * p
   ∎
```
