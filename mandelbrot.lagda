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
ni'o bau la .lojban.\ joi la'oi .Agda.\ la .varik.\ cu ciksi lo jai filri'a be tu'a le se cmima Coke me'oi .MANDELBROT.
\end{abstract}

\section{le vrici}

\begin{code}
open import Data.Nat
  using (
    ℕ
  )
open import Function
  using (
    _$_
  )
open import Data.Product
  using (
    ∃
  )
open import Relation.Nullary
  using (
    ¬_
  )
\end{code}

\section{la'oi .\F ℝ.}
ni'o la'oi .\F ℝ.\ ctaipe lo ro mrena'u... jenai zo'e

\begin{code}
ℝ : Set
ℝ = {!!}
\end{code}

\section{la'oi .\F ℂ.}
ni'o ro da zo'u da ctaipe la'oi .\F ℂ.\ jo cu lujna'u

\begin{code}
ℂ : Set
ℂ = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}>\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF{>} \B b\ .zoi.\ gi la'oi .\B a.\ zmadu la'oi .\B b.

\begin{code}
_>_ : ℝ → ℝ → Set
_>_ = {!!}
\end{code}

\section{la'o zoi.\ \F{∣\AgdaUnderscore{}∣}\ .zoi.}
ni'o la'o zoi.\ \F{∣\AgdaUnderscore{}∣}\ \B a\ .zoi.\ cu'alni la'oi .\B a.

\begin{code}
∣_∣ : ℂ → ℝ
∣_∣ = {!!}
\end{code}

\section{la'oi .\F{mf}.}
ni'o ga jonai\ldots
\begin{itemize}
	\item ga je la'oi .\B n.\ du la'o zoi.\ \IC{ℕ.zero}\ .zoi.\ gi ko'a goi la'o zoi.\ \F{mf} \B c \B n sumji ma lo tenfa be la'oi .\B c.\ bei li re gi
	\item ko'a sumji ma lo tenfa be fi li re bei lo mu'oi zoi.\ \F{mf} \B c\ .zoi.\ be lo lidne be la'oi .\B n.
\end{itemize}

\begin{code}
mf : ℂ → ℕ → ℂ
mf = {!!}
\end{code}

\section{la'oi .\F{MB}.}
ni'o ro da zo'u ga jo ctaipe lo me'oi .\F{MB}.\ be da gi da cmima le co'e Coke me'oi .MANDELBROT.

\begin{code}
MB : ℂ → Set
MB c = ∃ $ λ m → ¬_ $ ∃ $ λ n → (∣ mf c n ∣) > ∣ mf c m ∣
\end{code}
\end{document}
