\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{xcolor}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∄}{\ensuremath{\mathnormal\nexists}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{𝕗}{\ensuremath{\mathnormal{\mathbb{f}}}}
\newunicodechar{ℙ}{\ensuremath{\mathnormal{\mathbb{P}}}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb{F}}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb{S}}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb{M}}}}
\newunicodechar{ℝ}{\ensuremath{\mathnormal{\mathbb{R}}}}
\newunicodechar{ℂ}{\ensuremath{\mathnormal{\mathbb{C}}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb{B}}}}
\newunicodechar{ν}{\ensuremath{\mathnormal{\nu}}}
\newunicodechar{μ}{\ensuremath{\mathnormal{\mu}}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\phi}}}
\newunicodechar{χ}{\ensuremath{\mathnormal{\chi}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\wedge}}}
\newunicodechar{∅}{\ensuremath{\mathnormal{\emptyset}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{⁇}{\ensuremath{\mathnormal{\mathrm{?\!?}}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{σ}{\ensuremath{\mathnormal{\sigma}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\mathsf{m}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\mathsf{s}}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{⍉}{\ensuremath{\mathnormal{∘\hspace{-0.455em}\backslash}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_p}}}
\newunicodechar{ₙ}{\ensuremath{\mathnormal{_n}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{′}{\ensuremath{\mathnormal{'}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≗}{\ensuremath{\mathnormal{\circeq}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\title{le me'oi .Agda.\ ke me'oi .MANDELBROT.\ se cmima co'e}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{abstract}
\noindent
ni'o bau la .lojban.\ joi la'oi .Agda.\ la .varik.\ cu ciksi lo jai filri'a be tu'a le se cmima Coke me'oi .MANDELBROT.
\end{abstract}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

open import Data.Nat
  using (
    ℕ
  )
open import Function
  using (
    _∋_;
    _$_
  )
open import Data.Product
  using (
    proj₁;
    _×_;
    _,_;
    ∃
  )
open import Relation.Nullary
  using (
    ¬_
  )
\end{code}

\section{la'oi .\F ℝ.}
ni'o la'oi .\F ℝ.\ ctaipe lo ro mrena'u\ldots{}\ jenai zo'e

\begin{code}
ℝ : Set
ℝ = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}>\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF{>} \B b\ .zoi.\ gi la'oi .\B a.\ zmadu la'oi .\B b.

\begin{code}
_>_ : ℝ → ℝ → Set
_>_ = {!!}
\end{code}

\section{la'oi .\F ℂ.}
ni'o ro da zo'u da ctaipe la'oi .\F ℂ.\ jo cu lujna'u  .i la'o zoi.\ \IC{\AgdaUnderscore{},\AgdaUnderscore} \B a \B b\ .zoi.\ poi ke'a ctaipe la'oi .\F ℂ.\ cu sumji la'oi .\B a.\ lo pilji be la'oi .\B b.\ bei lo tenfa be li re bei li pa fi'u re

\begin{code}
ℂ : Set
ℂ = ℝ × ℝ
\end{code}

\section{la'o zoi.\ \F{AgdaUnderscore{}+\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \OpF + \B b\ .zoi.\ sumji la'oi .\B a.\ la'oi .\B b.

\begin{code}
_+_ : ℂ → ℂ → ℂ
_+_ = {!!}
\end{code}

\section{la \F{frinu}}
ni'o ga je la'o zoi.\ \F{frinu} \B a \B b \B c\ .zoi.\ frinu la'oi .\B a.\ la'oi .\B b.\ gi la'oi .\B c.\ ctiape le su'u la'oi .\B b.\ na du li no

\begin{code}
frinu : ℂ → ℂ → Set ∋ {!!} → ℂ
frinu = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}\textasciicircum\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \OpF{\textasciicircum} \B b\ .zoi.\ tenfa la'oi .\B a.\ la'oi .\B b.

\begin{code}
_^_ : ℂ → ℂ → ℂ
_^_ = {!!}
\end{code}

\section{la'o zoi.\ \F{ℕ→ℂ}\ .zoi.}
ni'o la'o zoi.\ \F{ℕ→ℂ} \B n\ .zoi.\ co'e du la'oi .\B n.

\begin{code}
ℕ→ℂ : ℕ → ℂ
ℕ→ℂ = {!!}
\end{code}

\section{la'o zoi.\ \F{∣\AgdaUnderscore{}∣}\ .zoi.}
ni'o la'o zoi.\ \F{∣\AgdaUnderscore{}∣}\ \B a\ .zoi.\ cu'alni la'oi .\B a.

\begin{code}
∣_∣ : ℂ → ℝ
∣_∣ (a , b) = proj₁ $ ((a' ^ 2ℂ) + (b' ^ 2ℂ)) ^ {!!}
  where
  2ℂ = ℕ→ℂ 2
  a' = {!!}
  b' = {!!}
\end{code}

\section{la'oi .\F{mf}.}
ni'o ga jonai\ldots
\begin{itemize}
	\item ga je la'oi .\B n.\ du la'o zoi.\ \IC{ℕ.zero}\ .zoi.\ gi la'oi .\B c.\ du ko'a goi la'o zoi.\ gi
	\item ko'a sumji la'oi .\B c.\ bei lo tenfa be fi li re bei fe lo mu'oi zoi.\ \F{mf} \B c\ .zoi.\ be lo lidne be la'oi .\B n.
\end{itemize}

\begin{code}
mf : ℂ → ℕ → ℂ
mf c ℕ.zero = c
mf c (ℕ.suc n) = c +_ $ (mf c n) ^ {!!}
\end{code}

\section{la'oi .\F{MB}.}
ni'o ro da zo'u ga jo ctaipe lo me'oi .\F{MB}.\ be da gi da cmima le co'e Coke me'oi .MANDELBROT.

\begin{code}
MB : ℂ → Set
MB c = ∃ $ λ m → ¬_ $ ∃ $ λ n → (∣ mf c n ∣) > ∣ mf c m ∣
\end{code}
\end{document}
