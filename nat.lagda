\documentclass{article}
%\usepackage[T1]{fontenc}
\usepackage[french]{babel}
\usepackage{csquotes}
\usepackage{agda}
\usepackage{amssymb}
\usepackage{mnsymbol}

\usepackage{newunicodechar}    % Pour \qed.
\newcommand{\nuc}[2]{\newunicodechar{#1}{\ensuremath{#2}}}
\nuc{ℕ}{\mathbb N}
\nuc{≡}{\equiv}
\nuc{⟨}{\langle}
\nuc{⟩}{\rangle}
\nuc{∎}{\blacksquare}
\nuc{∸}{\dotminus}

\begin{document}

\section{Naturals}

\subsection{Exercice \texttt{seven}}
Salut Victor.
Là on va importer les naturels.
\begin{code}
module nat where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
\end{code}
Vic: On définit avec des "\_" pour écrire a+b au lieu d'écrire \_+\_ a b ?
Encore bonjour.
Voici du code;
en particulier celui du nombre bien connu \(7\).
\begin{code}
sept = suc (suc (suc (suc (suc (suc (suc zero))))))
\end{code}

\subsection{Exercice \texttt{+-example}}
On importe le bordel pour les égalités propositionnelles.
\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
\end{code}
Maintenant le \enquote{calcul} de $3 + 4$.
\begin{code}
_ : 3 + 4 ≡ 7 -- je ne comprends pas cette ligne
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc 2 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc 1 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc 0 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎
\end{code}

\subsection{Exercice \texttt{*-example}}
La même chose pour la multiplication maintenant.
\begin{code}
_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    suc 2 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (suc 1 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (suc 0 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎
\end{code}

\subsection{Exercice \texttt{\_\^\_}}
Et l'exponentiation.
\begin{code}
_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ suc n = m * (m ^ n)
\end{code}
Le calcul de \verb|3 ^ 4|.
\begin{code}
_ : 3 ^ 4 ≡ 81
_ = refl
\end{code}

\subsection{\texttt{∸}}
Plus tard déso.

\subsection{Exercice \texttt{Bin}}
\begin{code}
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin -> Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = 2 * from b
from (b I) = 2 * from b + 1
\end{code}
\end{document}
