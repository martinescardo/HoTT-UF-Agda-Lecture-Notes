Solving the exercises
--- 

We can use all the Agda definitions defined in the lectures (`HoTT-UF-Agda.lagda`)
to solve the exercises. One way to do that is by installing this repository 
as an Agda library ([Library Management](https://agda.readthedocs.io/en/v2.6.0/tools/package-system.html)).

We can install this library using the tool [`agda/agda-pkg`](https://github.com/agda/agda-pkg) to make easier the process, but you must have `python-3.6` and [`pip`](https://pypi.org/project/agda-pkg/) to install this tool.

```
$ pip install agda-pkg 
$ agda-pkg init  
``` 

We install this library by running the following command:

```
$ agda-pkg install HoTT-UF-Agda
```

or the latest commit on github by running the following command:

```
$ agda-pkg install --github martinescardo/HoTT-UF-Agda-Lecture-Notes
```

Then, we can use the definitions by importing all the definitions using `open import HoTT-UF-Agda` like
in the following example (see the file `playground.lagda`):


```agda
$ cat playground.lagda
...
\begin{code}
open import HoTT-UF-Agda


ex1 : ∀ {x y : ℕ} → x ℕ-order.≤ y → Σ λ (z : ℕ) → x Arithmetic.+ z ≡ y
ex1 = {!   !}  --   ← Fill this hole!
\end{code}
...
``` 

Notice this example is a literate Agda file but you could import the
library in a normal file as it follows.


```agda
$ cat playground.agda
...
open import HoTT-UF-Agda

ex1 : ∀ {x y : ℕ} → x ℕ-order.≤ y → Σ λ (z : ℕ) → x Arithmetic.+ z ≡ y
ex1 = {!   !}  --   ← Fill this hole!
...
``` 

