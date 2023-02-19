# Introduction

This module is an initial exploration on how to define and present all the definitions for a game, a very simplistic game.

```agda
module simple where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

+-assoc : Set
+-assoc = ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z


+-assoc-proof : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-assoc-proof zero y z = refl
+-assoc-proof (suc x) y z = cong suc {! +-assoc-proof x y z!}
```
