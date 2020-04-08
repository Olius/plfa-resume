import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-idʳ : ∀ (m : ℕ) → m + zero ≡ m
+-idʳ zero = refl
+-idʳ (suc m) rewrite +-idʳ m = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-idʳ m
+-comm m (suc n) rewrite +-comm n m = +-suc m n

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p)
                   | sym (+-assoc n m p)
                   | +-comm m n
                   = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p
                              | +-assoc p (m * p) (n * p)
                              = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p
                          | *-assoc m n p
                          = refl

*-absʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-absʳ zero = refl
*-absʳ (suc m) = *-absʳ m

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n
                      | +-swap n m (m * n)
                      = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero = *-absʳ m
*-comm m (suc n) rewrite *-comm n m
                       = *-suc m n

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite 0∸n≡0 n
                         | 0∸n≡0 p
                         | 0∸n≡0 (n + p)
                         = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p = ∸-+-assoc m n p

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-idʳ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p rewrite ^-distribˡ-+-* m n p
                                 | *-assoc m (m ^ n) (m ^ p)
                                 = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p
                               | sym (*-assoc (m * n) (m ^ p) (n ^ p))
                               | *-assoc m n (m ^ p)
                               | *-comm n (m ^ p)
                               | sym (*-assoc m (m ^ p) n)
                               | *-assoc (m * (m ^ p)) n (n ^ p)
                               = refl

*-absˡ : ∀ (n : ℕ) → 1 ^ n ≡ 1
*-absˡ zero = refl
*-absˡ (suc n) rewrite +-idʳ (1 ^ n)
                     = *-absˡ n

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m zero p = *-absˡ p
^-*-assoc m (suc n) p rewrite ^-distribʳ-* m (m ^ n) p
                            | ^-distribˡ-+-* m p (n * p)
                            | ^-distribʳ-* m n p
                            | ^-*-assoc m n p
                            = refl

open import nat using (Bin; ⟨⟩; _O; _I; inc; from; to)

comm-sq-from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
comm-sq-from ⟨⟩ = refl
comm-sq-from (b O) rewrite +-comm (from b + (from b + zero)) 1 = refl
comm-sq-from (b I) rewrite comm-sq-from b
                         | +-assoc (from b) (from b + 0) 1
                         | +-comm (from b + 0) 1
                         = refl
to' : ℕ       → Bin
to'   0       = ⟨⟩
to'   (suc n) = inc (to' n)

-- to (from ⟨⟩)

-- to'-from : ∀ (b : Bin) → to' (from b) ≡ b
-- to'-from ⟨⟩ = refl
-- to'-from (b O) = {!!}
-- to'-from (b I) = {!!}

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) rewrite comm-sq-from (to n)
                      | from-to n
                      = refl
