module Beyond where

open import Agda.Builtin.Equality

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)

two : Nat
two = suc (suc zero)

four : Nat
four = suc (suc two)

twoPlusTwo : (two + two) ≡ four
twoPlusTwo = refl

zeroPlus : (n : Nat) → (zero + n) ≡ n
zeroPlus n = refl

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

plusZero : (n : Nat) → (n + zero) ≡ n
plusZero zero    = refl
plusZero (suc k) = cong suc (plusZero k)
