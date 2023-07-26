# Negative Logic

Exercises from http://conal.net/misc/negative-logic.pdf

## Exercise 1.1

```agda
module conal-exercises.negative-logic where

open import Data.Bool
open import Relation.Binary.PropositionalEquality as Eq
private variable x y : Bool
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


⟦_⟧ : Bool → Bool
⟦_⟧ = not

false' : Bool
false' = true

true' : Bool
true' = false

⟦false'⟧ : ⟦ false' ⟧ ≡ false
⟦false'⟧ =
  begin
    ⟦ false' ⟧
  ≡⟨⟩
    ⟦ true ⟧
  ≡⟨⟩
    not true
  ≡⟨⟩
    false
  ∎

⟦true'⟧ : ⟦ true' ⟧ ≡ true
⟦true'⟧ =
  begin
    ⟦ true' ⟧
  ≡⟨⟩
    ⟦ false ⟧
  ≡⟨⟩
    not false
  ≡⟨⟩
    true
  ∎
```

## Exercise 1.2. Define not' (implementation) and ⟦not'⟧ (correctness proof).

```agda
not' : Bool → Bool
not' = not

⟦not'⟧ : ∀ x → ⟦ not' x ⟧ ≡ not ⟦ x ⟧
⟦not'⟧ true =
  begin
    ⟦ not' true ⟧
  ≡⟨⟩
    ⟦ false ⟧
  ≡⟨⟩
   not ⟦ true ⟧
  ∎
⟦not'⟧ false =
  begin
    ⟦ not' false ⟧
  ≡⟨⟩
    ⟦ true ⟧
  ≡⟨⟩
   not ⟦ false ⟧
  ∎
```

## Exercise 1.3. Define _∧'_ and ⟦_∧'_⟧.

```agda
infixr 6 _∧'_ _⟦∧'⟧_

_∧'_ : Bool → Bool → Bool
_∧'_ =  _∨_

_⟦∧'⟧_ : ∀ x y → ⟦ x ∧' y ⟧ ≡ ⟦ x ⟧ ∧ ⟦ y ⟧
false ⟦∧'⟧ y =
  begin
    ⟦ false ∧' y ⟧
  ≡⟨⟩
    ⟦ false ∨ y ⟧
  ≡⟨⟩
    ⟦ y ⟧
  ≡⟨⟩
   ⟦ false ⟧ ∧ ⟦ y ⟧
  ∎
true ⟦∧'⟧ y =
  begin
    ⟦ true ∧' y ⟧
  ≡⟨⟩
    ⟦ true ∨ y ⟧
  ≡⟨⟩
    ⟦ true ⟧
  ≡⟨⟩
   ⟦ true ⟧ ∧ ⟦ y ⟧
  ∎
```

## Exercise 1.4. Likewise for disjunction _∨'_ and ⟦_∨'_⟧.

```agda
infixr 6 _∨'_ _⟦∨'⟧_

_∨'_ : Bool → Bool → Bool
_∨'_ =  _∧_

_⟦∨'⟧_ : ∀ x y → ⟦ x ∨' y ⟧ ≡ ⟦ x ⟧ ∨ ⟦ y ⟧
false ⟦∨'⟧ y =
  begin
    ⟦ false ∨' y ⟧
  ≡⟨⟩
    ⟦ false ∧ y ⟧
  ≡⟨⟩
    ⟦ false ⟧
  ≡⟨⟩
   ⟦ false ⟧ ∨ ⟦ y ⟧
  ∎
true ⟦∨'⟧ y =
  begin
    ⟦ true ∨' y ⟧
  ≡⟨⟩
    ⟦ true ∧ y ⟧
  ≡⟨⟩
    ⟦ y ⟧
  ≡⟨⟩
   ⟦ true ⟧ ∨ ⟦ y ⟧
  ∎
```

## Exercise 1.5. Likewise for exclusive-or

```agda
infixr 6 _xor'_ _⟦xor'⟧_

_xor'_ : Bool → Bool → Bool
x xor' y =  not (x xor y)

_⟦xor'⟧_ : ∀ x y → ⟦ x xor' y ⟧ ≡ ⟦ x ⟧ xor ⟦ y ⟧
false ⟦xor'⟧ false = refl
false ⟦xor'⟧ true = refl
true ⟦xor'⟧ false = refl
true ⟦xor'⟧ true = refl
```

## Exercise 1.6. Prove that `not'` is its own inverse

TODO. Comment that the signature was incomplete (∀ x →)

```agda
not'-involutive : ∀ x → not' (not' x) ≡ x
not'-involutive false =
  begin
    not' (not' false)
  ≡⟨⟩
   not' true
  ≡⟨⟩
   false
  ∎
not'-involutive true = refl
```

## Excercise 1.7. Prove that _∧'_ is associative, commutative and idempotent

```agda
import Data.Bool.Properties as BP

∧-comm : ∀ x y → x ∧' y ≡ y ∧' x
∧-comm x y =
  begin
    x ∧' y
  ≡⟨⟩
   x ∨ y
  ≡⟨ BP.∨-comm x y ⟩
   y ∨ x
  ≡⟨⟩
   y ∧' x
  ∎

∧0 : ∀ x → x ∧' false' ≡ false'
∧0 x =
  begin
    x ∧' false'
  ≡⟨⟩
   x ∧' true
  ≡⟨⟩
   x ∨ true
  ≡⟨ BP.∨-comm x true  ⟩
   true ∨ x
  ≡⟨⟩
   true
  ≡⟨⟩
   false'
  ∎

∨-idem : ∀ x → x ∨' x ≡ x
∨-idem x =
  begin
    x ∨' x
  ≡⟨⟩
   x ∧ x
  ≡⟨ BP.∧-idem x ⟩
   x
  ∎
```
