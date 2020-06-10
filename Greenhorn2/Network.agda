{-# OPTIONS --cubical --safe #-}
open import Cubical.Core.Everything
open import Cubical.Data.Nat renaming ( _+_     to plus
                                      ; +-assoc to plus-assoc
                                      ; +-suc   to plus-suc )
open import Cubical.Data.NatPlusOne

module Greenhorn2.Network (ℓ ℓ₁   : Level)
                          (State  : ℕ₊₁ → Type ℓ)
                          (Memory : ℕ₊₁ → Type ℓ₁) where

open Cubical.Data.NatPlusOne public

_+_ : ℕ₊₁ → ℕ₊₁ → ℕ₊₁
(1+ x) + (1+ y) = 2+ (plus x y)

+-assoc : (m n p : ℕ₊₁) → m + (n + p) ≡ (m + n) + p
+-assoc (1+ m) (1+ n) (1+ p) i =
  hcomp (λ j → λ { (i = i0) → 2+ (plus m (suc (plus n p)))
                 ; (i = i1) → hcomp (λ _ → λ { (j = i0) → 2+ (suc (plus m (plus n p)))
                                             ; (j = i1) → 2+ (suc (plus (plus m n) p)) })
                                    (2+ (suc (plus-assoc m n p j))) })
        (2+ (plus-suc m (plus n p) i))

data 𝔾 : ℕ₊₁ → ℕ₊₁ → Type (ℓ-max ℓ ℓ₁)
id : (m : ℕ₊₁) → 𝔾 m m
seq' : {m n p q : ℕ₊₁} → 𝔾 m n → n ≡ p → 𝔾 p q → 𝔾 m q

data 𝔾 where
  process : {m : ℕ₊₁} → State m → 𝔾 m 1
  edge : (m : ℕ₊₁) → 𝔾 1 m
  seq : {m n p : ℕ₊₁} → 𝔾 m n → 𝔾 n p → 𝔾 m p
  par : {m n p q : ℕ₊₁} → 𝔾 m n → 𝔾 p q → 𝔾 (m + p) (n + q)
  swap : (m n : ℕ₊₁) → 𝔾 (m + n) (n + m)
  loop : {m n s : ℕ₊₁} → Memory s → 𝔾 (m + s) (n + s) → 𝔾 m n
  seq-λ : {m n : ℕ₊₁} → (x : 𝔾 m n) → seq (id m) x ≡ x
  seq-ρ : {m n : ℕ₊₁} → (x : 𝔾 m n) → seq x (id n) ≡ x
  seq-α : {m n p q : ℕ₊₁} →
          (x : 𝔾 m n) →
          (y : 𝔾 n p) →
          (z : 𝔾 p q) →
          seq x (seq y z) ≡ seq (seq x y) z
  par-α : {m n p q r s : ℕ₊₁} →
        (x : 𝔾 m n) →
        (y : 𝔾 p q) →
        (z : 𝔾 r s) →
        PathP (λ i → 𝔾 (+-assoc m p r i) (+-assoc n q s i))
              (par x (par y z))
              (par (par x y) z)
  abiding : {m n p q r s : ℕ₊₁} →
            (w : 𝔾 m n) →
            (x : 𝔾 n p) →
            (y : 𝔾 q r) →
            (z : 𝔾 r s) →
            par (seq w x) (seq y z) ≡ seq (par w y) (par x z)
  swap-+ : {m n p : ℕ₊₁} →
           PathP (λ i → 𝔾 (+-assoc m n p i) (+-assoc n p m (~ i)))
                 (swap m (n + p))
                 (seq' (par (swap m n) (id p))
                       (λ i → +-assoc n m p (~ i))
                       (par (id n) (swap m p)))
  swap-law : {m n p q : ℕ₊₁} →
             (x : 𝔾 n p) →
             (y : 𝔾 m q) →
             seq (seq (swap m n) (par x y)) (swap p q) ≡ par y x
  no-cycles : {m n s : ℕ₊₁} →
              (mem : Memory s) →
              (x : 𝔾 m n) →
              (y : 𝔾 s s) →
              loop mem (par x y) ≡ x
  shift-loop : {m n p q s : ℕ₊₁} →
               (mem : Memory s) →
               (x : 𝔾 m n) →
               (y : 𝔾 (p + s) (q + s)) →
               Path (𝔾 (m + p) (n + q))
                    (loop mem
                          (transp (λ i → 𝔾 (+-assoc m p s i) (+-assoc n q s i))
                                  i0
                                  (par x y)))
                    (par x (loop mem y))

id one    = edge 1
id (2+ m) = par (edge 1) (id (1+ m))

seq' {m} x p y = seq (transp (λ i → 𝔾 m (p i)) i0 x) y
