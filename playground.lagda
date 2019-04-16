Solutions:

Import all the definitions from the lecture:
\begin{code}
open import HoTT-UF-Agda
\end{code}


Exercise No. 1:

\begin{code}
ex1 : ∀ {x y : ℕ} → x ℕ-order.≤ y → Σ λ (z : ℕ) → x Arithmetic.+ z ≡ y
ex1 = {!   !}  --   ← Fill this hole!
\end{code}
